(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxPlan FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require Import AcAst AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HB Require Import HxSurg HarnFam HarnLoop HarnSite HarnFk AcFam3 HarnChain HarnLongL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition obj_io (r : Z) (S : sst) : option (nat * Z) := find_idx (s_rgs S) (rgk S r) 0.
Definition b0_lin (r : Z) (S : sst) : option lin :=
  match obj_io r S with
  | Some (i, o) => match nth_error (s_rgs S) i with
                   | Some R => match tget (okey o) (rg_cont R) with Some (BV l 0) => Some l | _ => None end
                   | None => None
                   end
  | None => None
  end.
(* [comment removed for export] *)
Definition halfx (b r : Z) (S : sst) : option lin := match b0_lin r S with Some l => ldivz (laddc l (- b)) 2 | None => None end.
Definition v_last (S : sst) : positive := Pos.pred (s_next S).
Definition v_prev (S : sst) : positive := Pos.pred (Pos.pred (s_next S)).
Definition par_form (S : sst) : lin := ladd (lscale 2 (lvar (v_prev S))) (lvar (v_last S)).
Definition par_cell (r : Z) (S : sst) : option (nat * Z * lin) := match obj_io r S with Some (i, o) => Some (i, o, par_form S) | None => None end.
(* [comment removed for export] *)
Definition par_var (r : Z) (S : sst) : option lin :=
  match b0_lin r S with
  | Some l => match List.filter (fun '(_, c) => Z.eqb c 1) (l_t l) with [(x, _)] => Some (lvar x) | _ => None end
  | None => None
  end.
Definition PARREP_S (r : Z) (k : MCH) : MCH :=
  NODE (HNAMEL (halfx 0 r)) (NODE (HNAMEL (fun _ => Some (lconst 0))) (NODE (HREPL1 (par_cell r)) (NODE (HPSR (par_var r)) k))).
Definition PARREP_H (r : Z) (k : MCH) : MCH :=
  NODE (HNAMEL (halfx 1 r)) (NODE (HNAMEL (fun _ => Some (lconst 1))) (NODE (HREPL (par_cell r)) (NODE (HPSR (par_var r)) k))).
(* [comment removed for export] *)
Definition w2_cell (r : Z) (S : sst) : option (nat * Z) := match obj_io r S with Some (i, o) => Some (i, o + 16) | None => None end.
(* [comment removed for export] *)
Definition STASH_S (k : nat) (r : Z) (c : MCH) : MCH :=
  PARREP_S r (NODE (HTRK (w2_cell r)) (NODE (HPSRK 41 (fun _ => Some (lconst 17))) (A3N (NStashNil k r) c))).
(* [comment removed for export] *)
Definition ptr_of (r : Z) (S : sst) : lin := tb_heap r S.
Definition STASH_H (k : nat) (r : Z) (c : MCH) : MCH :=
  PARREP_H r
   (SURG (SFront (fun S => find_base (s_rgs S) (oshadow (ptr_of r S)) 0))
   (SURG (SFront (fun S => find_base (s_rgs S) (ptr_of r S) 0))
   (SURG (SFront (fun S => find_base (s_rgs S) (laddc (ptr_of r S) (-16)) 0))
   (A3N (NStash k 0 0 1 2) c)))).
(* [comment removed for export] *)
