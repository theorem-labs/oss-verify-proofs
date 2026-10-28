(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Uint63 PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType Run.
From OssFuzzTheorems.openssl.echconfiglist_parser.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import W64 ITrie FxInstr FxState FxMem FxExec FxImage FxHandoff FxHoBuild FxHandoff2.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsCert Require Import AsImages AsPlanImages.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrGen BrDress.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Common Require Import HoBridge.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsHole Require Import ES6Img.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.AsExit Require Import FePcs FeLib.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition FE_ENTRY : Z := 0x1a6068.      (* [comment removed for export] *)
Definition FE_RET   : Z := 0x1a66d8.      (* [comment removed for export] *)
Definition FE_GLB   : Z := 0x5edfa0.      (* [comment removed for export] *)
Definition FE_NGLB  : Z := 11850.         (* [comment removed for export] *)
Definition FE_STK   : Z := 512.           (* [comment removed for export] *)
Definition FE_SPLO  : Z := 0x100000000.    (* [comment removed for export] *)
Definition FE_SPHI  : Z := 0x7fffffffffff. (* [comment removed for export] *)
Definition FE_SH_LO : Z := 0x7fffa000.    (* [comment removed for export] *)
Definition FE_SH_HI : Z := 0x80178800.    (* [comment removed for export] *)
Definition FE_STEPS : Z := 897730.

Definition T_SP : int := 2%uint63.
Definition T_SH : int := 4%uint63.
Definition T_REG (r : Z) : int := ioz (100 + r).

(* [comment removed for export] *)
Definition FE_CELLS : list (Z * nat * Z) :=
  [(0x5eaa70, 8%nat, 0x569e10); (0x6a8110, 4%nat, 1); (0x6a81b0, 8%nat, 0); (0x6aa15c, 1%nat, 1); (0x6ab5d8, 1%nat, 1);
   (0x6aa8f8, 8%nat, 0x7fff8000); (0x73c4a0, 8%nat, 0xffffffffffffffff)].

(* [comment removed for export] *)
Definition FE_CLEAR : list (Z * Z) := [(0x10000, 0x195000); (0x195000, 0x571000); (0x571000, 0x5ea000); (0x5edf70, 0x5edf88); (0x5edf90, 0x6a7220)].
  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition FE_WR_PAGES : list Z := [0x6a8; 0xbdd; 0xbdf; 0xbe1].

(* [comment removed for export] *)
Definition FE_SAVED : list Z := [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fe_code : itrie finstr := odflt iempty (build_code ASEGS fe_pcs).
Lemma fe_code_eq : build_code ASEGS fe_pcs = Some fe_code.
Proof. vm_cast_no_check (eq_refl (Some fe_code)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fe_regs_opaque : list hfact :=
  map (fun r => HReg (ioz r) (FV (T_REG r) w_zero))
      [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31].
Definition fe_regs : list hfact :=
  [hreg 1 0%uint63 FE_RET; hreg 2 T_SP FE_STK; hreg 10 0%uint63 FE_GLB; hreg 11 0%uint63 FE_NGLB].
Definition fe_clear : list hfact := map (fun iv => hclear (fst iv) (snd iv)) FE_CLEAR.
Definition fe_cells : list hfact := map (fun c => match c with (a, n, v) => hcell 0%uint63 a n v end) FE_CELLS.
Definition fe_geom : list hfact :=
  [hregion T_SP 0 FE_STK 4; hwr T_SP 0 FE_STK;
   hregion T_SH FE_SH_LO FE_SH_HI 12; hwr T_SH FE_SH_LO (FE_SH_HI - FE_SH_LO);
   hdisj 0%uint63 0x10000 0xc04000 T_SP 0 FE_STK; hdisj 0%uint63 0x10000 0xc04000 T_SH FE_SH_LO FE_SH_HI;
   hdisj T_SH FE_SH_LO FE_SH_HI T_SP 0 FE_STK].
Definition fe_facts : list hfact := fe_regs_opaque ++ fe_regs ++ fe_clear ++ fe_cells ++ fe_geom.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zrange (fuel : nat) (a : Z) : list Z :=
  match fuel with O => [] | S f => a :: zrange f (a + 1) end.
Definition zpages (lo hi : Z) : list Z := zrange (Z.to_nat (hi - lo)) lo.   (* [comment removed for export] *)
Definition zcells (lo hi : Z) : list int := map (fun c => ioz c) (zrange (Z.to_nat (hi - lo)) lo).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition fe_fact_cells : itrie (list (int * cell)) :=
  fold_left (add_cell IM fe_facts 0%uint63) (flat_map (cells_of_fact fe_facts 0%uint63) fe_cells) iempty.
Definition cells_on (pn : Z) : list (int * cell) := odflt [] (iget (ioz pn) fe_fact_cells).

Definition cu_cells (lo hi : Z) : list (int * cell) := map (fun ci => (ci, CU)) (zcells lo hi).

(* [comment removed for export] *)
Definition fe_rw_page (pn : Z) : pdesc :=
  if (pn <? 0x5ea) || ((0x5ee <=? pn) && (pn <? 0x6a7)) then PD (ioz pn) false PKImage []       (* [comment removed for export] *)
  else if pn =? 0x5ed then PD (ioz pn) false PKImage (cu_cells 0 494 ++ cu_cells 497 498)          (* [comment removed for export] *)
  else if pn =? 0x6a7 then PD (ioz pn) false PKImage (cu_cells 68 512)                            (* [comment removed for export] *)
  else PD (ioz pn) (existsb (Z.eqb pn) FE_WR_PAGES) PKUnk (cells_on pn).
Definition fe_rw_pages : list pdesc := map fe_rw_page (zpages 0x571 0xc04).

Definition fe_regs_desc : list (int * fval) :=
  map (fun r => (ioz r, if r =? 1 then FV 0%uint63 (w_of_Z FE_RET) else if r =? 2 then FV T_SP (w_of_Z FE_STK)
                        else if r =? 10 then FV 0%uint63 (w_of_Z FE_GLB) else if r =? 11 then FV 0%uint63 (w_of_Z FE_NGLB)
                        else FV (T_REG r) w_zero))
      [1;2;3;4;5;6;7;8;9;10;11;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;28;29;30;31].

Definition fe_desc : sdesc :=
  SD (ioz FE_ENTRY) fe_regs_desc
     [RD 0%uint63 (ioz 0x10000) (ioz 0xc04000) 0%uint63 None fe_rw_pages;
      RD T_SP 0%uint63 (ioz FE_STK) 4%uint63 (Some PKUnk) [];
      RD T_SH (ioz FE_SH_LO) (ioz FE_SH_HI) 12%uint63 (Some PKUnk) []].

(* [comment removed for export] *)
Definition fe_dress : list ditem := [(T_SH, 0%uint63, 0%uint63, RK_plain)].
Notation fe_start := (dress (state_of fe_desc) fe_dress) (only parsing).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fe_check : ho_check2 IM fe_facts fe_desc = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma fe_summary_ok :
  run_summary IM fe_code (ioz FE_RET) 20%nat (dress (state_of fe_desc) fe_dress) FE_SAVED
  = (SBreak, FE_STEPS, None, FE_RET, FV T_SP (w_of_Z FE_STK), map (fun r => FV (T_REG r) w_zero) FE_SAVED).
Proof. vm_cast_no_check (eq_refl (run_summary IM fe_code (ioz FE_RET) 20%nat (dress (state_of fe_desc) fe_dress) FE_SAVED)). Qed.

(* [comment removed for export] *)
Lemma fe_wr_ok : wr_pages_chk IM fe_desc FE_WR_PAGES = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

(* [comment removed for export] *)
Lemma IM_shape :
  map (fun sg => (to_Z (sg_base sg), to_Z (sg_size sg), sg_wr sg)) IM
  = [(0x10000, 0x185000, false); (0x195000, 0x3dc000, false); (0x571000, 0x79000, true); (0x5ea000, 0x61a000, true)].
Proof. vm_cast_no_check (eq_refl (map (fun sg => (to_Z (sg_base sg), to_Z (sg_size sg), sg_wr sg)) IM)). Qed.
