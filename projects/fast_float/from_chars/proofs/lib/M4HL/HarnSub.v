(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxMem FxRgs FxFacts FxSubst FxEnt FxPlan FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxChDen FxChain FxChMain.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcAst AcSteps AcFam AcFam2.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXD Require Import AsanPNodes AsanBNodes AsanBodyE AsanBodyP.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HxSurg HarnFam AcFam3.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4HL Require Import HarnLoop HarnSite HarnFk HarnChain HarnBudget HarnDev.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition OBJ_OFF (t : nat) : Z := 32 + 64 * Z.of_nat t.
Definition CUTOBJ (k : MCH) : MCH :=
  SURG (SSteps (fun S => cut_at S (rgk S 10) 256 [(32, RW); (32, RW); (32, RW); (32, RW); (32, RW); (32, RW); (64, RW)])) k.
(* [comment removed for export] *)
Definition fk_cut_fsh10 (p : sst -> lin) (S : sst) : option (list rstep) :=
  cut_at S (p S) 32 [(4, RZ); (3, RZ); (1, RZ); (4, RZ); (3, RZ); (1, RZ); (4, RZ); (3, RZ); (1, RZ); (8, RZ)].
Definition CUTFSH7 (k : MCH) : MCH := SURG (SSteps (fk_cut_fsh10 (fun S => oshadow (rgk S 10)))) k.
(* [comment removed for export] *)
Definition ENTRY2 (k : MCH) : MCH :=
  MSegK 20 P_HH (KCons 0x900a0 0 (TRY (HIXF (fun S => Some (HINTof S 2))) (CARVE2 (MSegK 20 P_HH (KCons 0x900a4 0 (PROMZ2 (CUTFSH7 (CUTOBJ k))) KNil)))) KNil).
(* [comment removed for export] *)
Definition FRONT_AT (a : sst -> lin) (k : MCH) : MCH := SURG (SFront (fun S => find_base (s_rgs S) (a S) 0)) k.
(* [comment removed for export] *)
Definition frF (S : sst) : lin := rgk S 25.
Definition frSH (S : sst) : lin := rgk S 24.
(* [comment removed for export] *)
Definition objsh (j : nat) (S : sst) : lin := laddc (frSH S) (8 * Z.of_nat j + 4).
Definition objlo (j : nat) (S : sst) : lin := laddc (frSH S) (8 * Z.of_nat j).
Definition objhi (j : nat) (S : sst) : lin := laddc (frSH S) (8 * Z.of_nat j + 7).
(* [comment removed for export] *)
Definition FRONT4 (j : nat) (k : MCH) : MCH :=
  FRONT_AT (objhi j) (FRONT_AT (objsh j) (FRONT_AT (objlo j) (FRONT_AT (fun S => laddc (frF S) (OBJ_OFF j)) k))).
Definition FRONT6 (t : nat) (k : MCH) : MCH :=
  let o1 := match t with O => 1%nat | _ => O end in let o2 := match t with 2%nat => 1%nat | _ => 2%nat end in
  FRONT4 o2 (FRONT4 o1 (FRONT4 t k)).
(* [comment removed for export] *)
Fixpoint find_end (rgs : list region) (a : lin) (i : nat) : option nat :=
  match rgs with
  | [] => None
  | R :: rs => if lin_eqb (ladd (rg_base R) (rg_size R)) a then Some i else find_end rs a (S i)
  end.
Definition GROUP_FRONT (A : sst -> lin) (offs : list Z) (len : Z) (k : MCH) : MCH :=
  FRONT_AT (fun S => laddc (A S) len)
    (List.fold_right (fun o c => FRONT_AT (fun S => laddc (A S) o) c)
       (SURG (SFront (fun S => find_end (s_rgs S) (A S) 0)) k) (List.rev offs)).
Definition fr_offs : list Z := [0; 32; 64; 96; 128; 160; 192].
Definition win_offs : list Z := [0; 4; 7; 8; 12; 15; 16; 20; 23; 24].
(* [comment removed for export] *)
Definition fr_drop (S : sst) : option (list rstep) :=
  match find_base (s_rgs S) (frF S) 0 with Some i => Some (List.map (fun j => RDrop (i + j)%nat) (List.seq 0 7)) | None => None end.
Definition fr_mrg (o : Z) (S : sst) : option (nat * nat) := match find_base (s_rgs S) (laddc (frF S) o) 0 with Some i => Some (i, 3%nat) | None => None end.
Definition REGROUP (k : MCH) : MCH :=
  GROUP_FRONT frSH win_offs 32
    (GROUP_FRONT frF fr_offs 256
       (SURG (SSteps fr_drop) (SURG (SMerge (fr_mrg 0)) (SURG (SMerge (fr_mrg 96)) (SURG (SMerge (fr_mrg 0)) k))))).

(* [comment removed for export] *)
Definition obj_w (j : nat) (off : Z) (S : sst) : option (nat * Z) :=
  match find_idx (s_rgs S) (laddc (frF S) (OBJ_OFF j)) 0 with
  | Some (i, o) => match nth_error (s_rgs S) i with
                   | Some R => match tget (okey o) (rg_cont R) with Some _ => None | None => Some (i, o + off) end
                   | None => None
                   end
  | None => None
  end.
Definition NAMEOBJ (j : nat) (k : MCH) : MCH := TRY (HTRK (obj_w j 16)) (TRY (HTRK (obj_w j 0)) k).
(* [comment removed for export] *)
Definition WINPREP (t : nat) (k : MCH) : MCH :=
  TRY (HRBK (fun S => at_c S (laddc (frSH S) (8 * Z.of_nat t)) 4)) (TRY (HRB1 (fun S => at1 S (laddc (frSH S) (8 * Z.of_nat t + 7)))) k).
(* [comment removed for export] *)
Definition OBJSH_T (t : nat) (k : MCH) : MCH := TRY (HUNZ (fun S => find_base (s_rgs S) (objsh t S) 0)) k.
Definition OBJSH_O (j : nat) (k : MCH) : MCH := TRY (HRBK (fun S => at_c S (objsh j S) 3)) k.
Definition OBJ_LH (j : nat) (k : MCH) : MCH := TRY (HRBK (fun S => at_c S (objlo j S) 4)) (TRY (HRB1 (fun S => at1 S (objhi j S))) k).
(* [comment removed for export] *)
Definition is_barel (l : lin) : bool := match l_t l with [(_, 1)] => Z.eqb (l_c l) 0 | _ => false end.
Definition name_f (a : sst -> option lin) (S : sst) : option lin :=
  match a S with Some ad => match cell S ad with Some l => if is_barel l then None else Some l | None => None end | None => None end.
Definition name_r (a : sst -> option lin) (S : sst) : option (nat * Z * lin) :=
  match a S, s_facts S with
  | Some ad, FRange d 0 0 :: _ =>
      match cell S ad, find_idx (s_rgs S) ad 0 with
      | Some l, Some (i, o) => let y := lvar (Pos.pred (s_next S)) in if lin_eqb d (lsub y l) then Some (i, o, y) else None
      | _, _ => None
      end
  | _, _ => None
  end.
Definition NAMECELL (a : sst -> option lin) (k : MCH) : MCH := TRY (HNAMEL (name_f a)) (TRY (HREPL (name_r a)) k).
(* [comment removed for export] *)
Definition STATNAME (k : MCH) : MCH := NAMECELL (stat_at 0) (NAMECELL (stat_at 8) (NAMECELL (stat_at 16) (NAMECELL (stat_at 24) (NAMECELL (stat_at 32) k)))).
(* [comment removed for export] *)
Definition SITEPREP (t : nat) (k : MCH) : MCH :=
  let o1 := match t with O => 1%nat | _ => O end in let o2 := match t with 2%nat => 1%nat | _ => 2%nat end in
  NODE (HPSRK UKEY (fun _ => Some (lconst (Z.of_nat t)))) (STATNAME (NAMEOBJ o1 (NAMEOBJ o2 (OBJSH_T t (OBJSH_O o1 (OBJSH_O o2 (OBJ_LH 0 (OBJ_LH 1 (OBJ_LH 2 (FRONT6 t k)))))))))).

(* [comment removed for export] *)
Definition MSQ (stops : list Z) (k : MCH) : MCH := MSegK 20 (PRun F60000 (stops ++ [0x606b0]) []) (KCons 0x606b0 0 (NODE HQSM k) KNil).

(* [comment removed for export] *)
Definition fsh_drop7 (S : sst) : option (list rstep) :=
  match idx_at S (rgk S 24) with Some i => Some (List.map (fun j => RDrop (i + j)%nat) (List.seq 0 10)) | None => None end.
Definition EXIT7 (k : MCH) : MCH :=
  SURG (SSteps fsh_drop7) (SURG (SMerge (fun S => merge_at S (rgk S 24) 3)) (SURG (SMerge (fun S => merge_at S (rgk S 24) 3)) (SURG (SMerge (fun S => merge_at S (rgk S 24) 3))
  (SURG (SMerge (fun S => merge_at S (rgk S 24) 3)) (SURG (SMerge (fun S => merge_at S (rgk S 24) 2))
  (SURG (SMerge (fk_mrg3 (fun S => rgk S 24)))
  (SURG (SSteps (fk_drop (fun S => rgk S 25))) (NODE (HIXF (fun S => Some (rgk S 25))) (SURG (SMerge (fk_mrg3 (fun S => rgk S 25)))
  (TRY (HUNZ (fk_unz (fun S => rgk S 10))) (TRY (HPROMZ (fk_unz (fun S => rgk S 10))) (NODE (HIXF (fun S => Some (rgk S 10)))
  (SURG (SMerge (fk_mrg3 (fun S => rgk S 10))) k))))))))))))).
