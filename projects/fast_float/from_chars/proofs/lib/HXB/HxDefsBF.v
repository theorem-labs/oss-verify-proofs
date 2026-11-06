(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require PropExec FxLin FxCore FxSubst FxSound FxMem FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSound.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxEnt FxRgs FxFacts FxPlan FxFrame FxWork FxWorkX.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.PropExec OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound.FxGlue OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWorkX.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require Import KxBridge KxRun.
From OSSVerify.Proofs.fast_float.from_chars.lib.HX Require Import HxGen.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXB Require Import HxBaseB HxIntBF.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Definition P47 : Z := 2 ^ 47.
(* [comment removed for export] *)
Definition fp_of (L : sst) : option lin :=
  match find_cell (s_rgs L) (laddc (rgl L 9) 56) with Some (_, _, l) => Some l | None => None end.

(* [comment removed for export] *)
Definition nofrac_newx (L : sst) : list xfact := [XF 1 [rgl L 10; lconst 0; lconst 0; TXT_TL]].
Definition R_NOFRAC : xst -> option (list xst) := hx_rule 0x9b244 (fun _ => true) nofrac_newx.

(* [comment removed for export] *)
Definition dig0_chk (X : xst) : bool :=
  let L := xs_st X in
  (txt_rgs_ok L && forallb (fact_implied (s_facts L)) (txt_facts ++ [FRange (lsub (rgl L 12) TXT_T) 0 128; FRange (lsub TXT_TL (rgl L 12)) 0 128]))%bool.
Definition dig0_newx (L : sst) : list xfact := [XF 0 [rgl L 12; rgl L 12]].
Definition R_DIG0 : xst -> option (list xst) := hx_rule 0x9b0b8 dig0_chk dig0_newx.

(* [comment removed for export] *)
Definition SW8_KEYS : list Z := [1; 5; 6; 7; 11; 12; 14; 15; 18; 23; 24; 27].
Definition SW8_CONSTS : list (Z * Z) :=
  [(10, 10); (13, 7); (17, 14974415777481871312); (28, 9259542123273814144); (29, 5063812098665367110);
   (30, 100000000); (31, 4294967296000100); (25, 42949672960001); (26, 1095216660735)].
Definition sw8_facts (L : sst) : list fact :=
  let X := rgl L 24 in
  [FRange (lsub X TXT_T) 0 128; FRange (lsub TXT_TL X) 8 128; FRange (lsub (rgl L 11) (lsub TXT_TL X)) 0 0;
   FRange (lsub X (lscale 8 (laddc (rgl L 1) (- SHBz)))) 0 7; FRange (laddc (rgl L 1) (- SHBz)) 0 (2 ^ 48)].
Definition sw8_chk (X : xst) : bool :=
  let L := xs_st X in
  match s_resv L with
  | RNone => (txt_rgs_ok L && lin_eqb (rgl L 19) (lconst SHBz) && lin_eqb (rgl L 12) (laddc (rgl L 24) 7)
              && lin_eqb (rgl L 6) (rgl L 24) && lin_eqb (rgl L 16) (rgl L 27)
              && forallb (fun '(k, c) => lin_eqb (rgl L k) (lconst c)) SW8_CONSTS
              && forallb (fact_implied (s_facts L)) (txt_facts ++ sw8_facts L))%bool
  | _ => false
  end.
Definition sw8_newf (L : sst) : list fact :=
  let P' := lvar (fv (s_next L) 10) in
  [FRange (lsub P' (rgl L 24)) 0 128; FRange (lsub P' TXT_T) 0 128; FRange (lsub TXT_TL P') 0 128;
   FRange (lsub (lvar (fv (s_next L) 4)) (lsub TXT_TL P')) 0 0; FRange P' 6537216 P47].
Definition sw8_newfA (L : sst) : list fact :=
  FRange (lsub TXT_TL (lvar (fv (s_next L) 10))) 8 128 :: FRange (lsub (lvar (fv (s_next L) 2)) (lvar (fv (s_next L) 10))) 0 0 :: sw8_newf L.
Definition sw8_newfB (L : sst) : list fact :=
  let P' := lvar (fv (s_next L) 10) in
  FRange (lsub TXT_TL P') 0 7 :: FRange (lsub (lvar (fv (s_next L) 5)) (laddc P' 7)) 0 0 ::
  FRange (lsub (lvar (fv (s_next L) 11)) (rgl L 16)) 0 0 :: sw8_newf L.
Definition sw8_newx (L : sst) : list xfact := [XF 0 [rgl L 24; lvar (fv (s_next L) 10)]].
Definition SW8_EXITS : list hx_exit := [(0x9b6e0, sw8_newfA, sw8_newx); (0x9b700, sw8_newfB, sw8_newx)].
Definition H_SW8 : xst -> option (list xst) := hx_regm 0x9b14c SW8_KEYS sw8_chk SW8_EXITS.

(* [comment removed for export] *)
Definition SW4_KEYS : list Z := [6; 11; 12; 13; 14; 15; 24].
Definition sw4_facts (L : sst) : list fact :=
  let X := rgl L 24 in [FRange (lsub X TXT_T) 0 128; FRange (lsub TXT_TL X) 4 128; FRange (lsub (rgl L 6) X) 0 0].
Definition sw4c_facts (L : sst) : list fact :=
  let X := rgl L 24 in [FRange (lsub X TXT_T) 0 128; FRange (lsub TXT_TL X) 0 128; FRange (lsub (rgl L 6) X) 0 0;
                        FRange (lsub (rgl L 11) (lsub TXT_TL X)) 0 0].
Definition sw4g_chk (facts : sst -> list fact) (X : xst) : bool :=
  let L := xs_st X in
  match s_resv L, fp_of L with
  | RNone, Some FP => (txt_rgs_ok L && lin_eqb (rgl L 19) (lconst SHBz)
                       && forallb (fact_implied (s_facts L)) (txt_facts ++ facts L ++ [FRange (lsub FP TXT_T) 0 128])
                       && existsb (xf_eqb (XF 0 [FP; rgl L 24])) (xs_x X))%bool
  | _, _ => false
  end.
Definition sw4_chk : xst -> bool := sw4g_chk sw4_facts.
Definition sw4c_chk : xst -> bool := sw4g_chk sw4c_facts.
Definition fp_facts (L : sst) (P' : lin) : list fact :=
  match fp_of L with Some FP => [FRange (lsub P' FP) 0 128] | None => [] end.
Definition sw4_newf (L : sst) : list fact :=
  let P' := lvar (fv (s_next L) 6) in
  fp_facts L P' ++
  [FRange (lsub P' (rgl L 24)) 0 4; FRange (lsub P' TXT_T) 0 128; FRange (lsub TXT_TL P') 0 128; FRange (lsub (lvar (fv (s_next L) 0)) P') 0 0;
   FRange P' 6537216 P47].
Definition sw4_newx (L : sst) : list xfact :=
  match fp_of L with Some FP => [XF 0 [FP; lvar (fv (s_next L) 6)]] | None => [] end.
Definition H_SW4 : xst -> option (list xst) := hx_regm 0x9b724 SW4_KEYS sw4_chk [(0x9b7f4, sw4_newf, sw4_newx)].
Definition H_SW4C : xst -> option (list xst) := hx_regm 0x9b71c SW4_KEYS sw4c_chk [(0x9b7f4, sw4_newf, sw4_newx)].

(* [comment removed for export] *)
Definition BYTE_KEYS : list Z := [11; 12; 13; 14; 15; 16; 17; 24].
Definition byte_facts (L : sst) : list fact :=
  let X := rgl L 24 in [FRange (lsub X TXT_T) 0 128; FRange (lsub TXT_TL X) 0 128].
Definition byte_chk (X : xst) : bool :=
  let L := xs_st X in
  match s_resv L, fp_of L with
  | RNone, Some FP => (txt_rgs_ok L && lin_eqb (rgl L 19) (lconst SHBz) && lin_eqb (rgl L 22) TXT_TL
                       && forallb (fact_implied (s_facts L)) (txt_facts ++ byte_facts L ++ [FRange (lsub FP TXT_T) 0 128])
                       && existsb (xf_eqb (XF 0 [FP; rgl L 24])) (xs_x X))%bool
  | _, _ => false
  end.
Definition byte_newf (L : sst) : list fact :=
  let P' := lvar (fv (s_next L) 7) in
  fp_facts L P' ++
  [FRange (lsub P' (rgl L 24)) 0 128; FRange (lsub P' TXT_T) 0 128; FRange (lsub TXT_TL P') 0 128; FRange P' 6537216 P47].
Definition byte_newx (L : sst) : list xfact :=
  match fp_of L with Some FP => [XF 0 [FP; lvar (fv (s_next L) 7)]] | None => [] end.
Definition H_BYTE : xst -> option (list xst) := hx_regm 0x9b7f4 BYTE_KEYS byte_chk [(0x9b85c, byte_newf, byte_newx)].

(* [comment removed for export] *)
Definition frac_chk (X : xst) : bool :=
  let L := xs_st X in
  let IE := rgl L 10 in let FP := rgl L 29 in let FE := rgl L 24 in
  (txt_rgs_ok L && lin_eqb (rgl L 11) (lsub FE FP)
   && forallb (fact_implied (s_facts L))
        (txt_facts ++ [FRange (lsub FP (laddc IE 1)) 0 0; FRange (lsub IE TXT_T) 0 128; FRange (lsub TXT_TL FE) 0 128])
   && existsb (xf_eqb (XF 2 [IE])) (xs_x X) && existsb (xf_eqb (XF 0 [FP; FE])) (xs_x X))%bool.
Definition frac_newx (L : sst) : list xfact := [XF 1 [rgl L 10; rgl L 29; rgl L 11; TXT_TL]].
Definition R_FRAC : xst -> option (list xst) := hx_rule 0x9b888 frac_chk frac_newx.

(* [comment removed for export] *)
Definition EXPMAXz : Z := 2684354569.
Definition rod_ok (rgs : list region) : bool := existsb (fun R => rg_is R (lconst 65536) (lconst 188416) RO) rgs.
Definition TM_KEYS : list Z := [5; 6; 10; 11; 12; 13; 14; 15; 17; 28].
Definition fl_of (L : sst) : option lin :=
  match find_cell (s_rgs L) (laddc (rgl L 9) 48) with Some (_, _, l) => Some l | None => None end.
Definition tm_facts (L : sst) (fL : lin) : list fact :=
  let S := rgl L 21 in let IE := rgl L 10 in
  [FRange (lsub S TXT_T) 0 128; FRange (lsub IE S) 0 128; FRange (lsub TXT_TL IE) 0 128; FRange fL 0 128;
   FRange (rgl L 9) (2 ^ 40) (2 ^ 47); FRange (lsub (rgl L 6) (ladd (lsub IE S) fL)) 0 0; FRange (lsub (rgl L 16) (lsub IE S)) 0 0;
   FRange (laddc (rgl L 7) EXPMAXz) 0 (2 * EXPMAXz);
   FRange (rgl L 6) 20 256].      (* [comment removed for export] *)
Definition tm_chk (X : xst) : bool :=
  let L := xs_st X in
  match s_resv L, fl_of L with
  | RNone, Some fL =>
      (txt_rgs_ok L && lin_eqb (rgl L 22) TXT_TL && lin_eqb (rgl L 19) (lconst SHBz) && lin_eqb (rgl L 1) (lconst 46) && rod_ok (s_rgs L)
       && forallb (fact_implied (s_facts L)) (txt_facts ++ tm_facts L fL)
       && existsb (xf_eqb (XF 0 [rgl L 21; rgl L 10])) (xs_x X)
       && existsb (xf_eqb (XF 1 [rgl L 10; rgl L 29; fL; TXT_TL])) (xs_x X))%bool
  | _, _ => false
  end.
Definition tm_newf0 (L : sst) : list fact :=
  [FRange (lsub (lvar (fv (s_next L) 0)) (rgl L 5)) 0 0; FRange (lsub (lvar (fv (s_next L) 7)) (rgl L 15)) 0 0].
Definition tm_newf1 (L : sst) : list fact :=
  [FRange (lvar (fv (s_next L) 7)) 1 (10 ^ 19 - 1); FRange (laddc (lvar (fv (s_next L) 0)) (EXPMAXz + 128)) 0 (2 * EXPMAXz + 256)].
Definition TM_EXITS : list hx_exit := [(0x9c5f8, tm_newf0, nox); (0x9cc68, tm_newf1, nox)].
Definition H_TM : xst -> option (list xst) := hx_regm 0x9c504 TM_KEYS tm_chk TM_EXITS.
