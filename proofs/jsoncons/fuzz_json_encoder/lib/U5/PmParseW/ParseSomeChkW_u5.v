(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AsanPlanCore AsanPlanSound LibSym SegRun SegPlan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmEncSpecs_u5 PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import RelLeaf.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.CutCert Require Import CutCert CutOps CutHeap CutAuto CutLib CutHeap2 CutAutoX.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.CutGen Require Import Cut_psome_xsrcw_D_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSums_u5 ParseSums2_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseSomeKn. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseSpecs_u5. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.PmParse Require Import ParseProve. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParse Require Import ParseBridges_u5 ParseBridges2_u5 ParseBridges3_u5 ParseBridges4_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmParseW Require Import ParseSomeChk_u5 ParseSomeChk2_u5.
Import ListNotations. Import AX2.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Printing Width 1014832. Set Printing Depth 1014832.

Module PSCW.
Import PML PMR PSMC.
Module G := Cut_psome_xsrcw_D_u5.      (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition getc (i : nat) : CC.cutpoint := PSM2.cutn i.
Definition leafps (i k : nat) : SR.post_spec := nth k (CC.cp_PSS (getc i)) (SR.PS 0 [] [] []).
(* [comment removed for export] *)
Fixpoint pcell (off : Z) (w : nat) (cells : list kentry) : option expr :=
  match cells with
  | KWord (SA (EVar 10) o) w' e :: r => if (o =? off) && Nat.eqb w w' then Some e else pcell off w r
  | _ :: r => pcell off w r | [] => None end.
(* [comment removed for export] *)
Fixpoint named_bytes (nx : nat) (cells : list kentry) : list (saddr * nat) :=
  match cells with
  | KWord (SA base o) 1 (EVar v) :: r => (if match base with EVar 10 => false | _ => Nat.leb nx v end then [(SA base o, v)] else []) ++ named_bytes nx r
  | _ :: r => named_bytes nx r | [] => [] end.
Fixpoint min_var (l : list (saddr * nat)) (best : option (saddr * nat)) : option (saddr * nat) :=
  match l with
  | [] => best
  | (a, v) :: r => min_var r (match best with Some (_, v0) => if Nat.ltb v v0 then Some (a, v) else best | None => Some (a, v) end)
  end.
Definition leaf_byte (i k : nat) : option (saddr * nat) := min_var (named_bytes (CC.cp_nx (getc i)) (SR.ps_cells (leafps i k))) None.
(* [comment removed for export] *)
Definition leaf_st (i k : nat) : option Z :=
  match pcell 208 1 (CC.cp_know (getc i)) with
  | Some (ELit c) => Some c
  | Some (EVar s) => let r := PSM2.rng_of (SR.ps_cells (leafps i k)) (EVar s) in if fst r =? snd r then Some (fst r) else None
  | _ => None
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition act_eqb (a1 a2 : act) : bool :=
  match a1, a2 with
  | AErr c1 k1, AErr c2 k2 => (c1 =? c2) && Bool.eqb k1 k2 | AAccept, AAccept => true | ASkip, ASkip => true | ASlash, ASlash => true
  | ABegin x, ABegin y => Bool.eqb x y | AEnd x, AEnd y => Bool.eqb x y | AString x, AString y => Bool.eqb x y | ANumber, ANumber => true
  | ALit x, ALit y => x =? y | AComma, AComma => true | AGoto s1 k1, AGoto s2 k2 => (s1 =? s2) && Bool.eqb k1 k2 | APop k1, APop k2 => Bool.eqb k1 k2
  | APushCr, APushCr => true | ALitDone, ALitDone => true | AParseString, AParseString => true | AParseNumber, AParseNumber => true | AStuck, AStuck => true
  | _, _ => false
  end.
Lemma act_eqb_eq : forall a b, act_eqb a b = true -> a = b.
Proof.
  intros [] [] H; cbn in H; try discriminate; try reflexivity;
  repeat match goal with H : (_ && _) = true |- _ => apply andb_prop in H; destruct H as [? H] end;
  repeat match goal with H : (_ =? _) = true |- _ => apply Z.eqb_eq in H; subst end;
  repeat match goal with H : Bool.eqb _ _ = true |- _ => apply eqb_prop in H; subst end; reflexivity.
Qed.
(* [comment removed for export] *)
Definition PARENTS : list Z := [ST_ROOT; ST_OBJECT; ST_ARRAY; ST_MEMBER_NAME].
(* [comment removed for export] *)
Fixpoint first_adm (bv : nat) (cells : list kentry) (b : Z) (n : nat) : option Z :=
  match n with O => None | S n' => if RLF.byte_adm bv cells b then Some b else first_adm bv cells (b + 1) n' end.
(* [comment removed for export] *)
Definition NOBYTE_STATES : list Z := [ST_ROOT; ST_ACCEPT; ST_OBJECT; ST_ARRAY; ST_STRING; ST_MEMBER_NAME; ST_NUMBER; ST_DONE].
Definition leaf_act (i k : nat) : option (Z * option nat * act) :=
  match leaf_st i k with
  | None => None
  | Some st =>
    match leaf_byte i k with
    | Some (_, bv) => match first_adm bv (SR.ps_cells (leafps i k)) 0 256 with Some b => Some (st, Some bv, dispatch st ST_ROOT b) | None => None end
    | None => if existsb (Z.eqb st) NOBYTE_STATES then Some (st, None, dispatch st ST_ROOT 0) else None
    end
  end.
(* [comment removed for export] *)
Definition all_parents (f : Z -> bool) : bool := forallb f PARENTS.
Definition leaf_act_chk (i k : nat) : bool :=
  match leaf_act i k with
  | None => true
  | Some (st, Some bv, a) =>
      match leaf_byte i k, pcell 200 8 (CC.cp_know (getc i)) with
      | Some (SA base off, bv'), Some wp =>
          Nat.eqb bv bv' && expr_eqb base wp && (off =? 0) &&
          PB.has (SR.ps_cells (leafps i k)) (KWord (SA base off) 1 (EVar bv)) && PB.has (SR.ps_cells (leafps i k)) (KRange (EVar bv) 0 255) &&
          (* [comment removed for export] *)
          RLF.all_bytes (fun b => negb (RLF.byte_adm bv (SR.ps_cells (leafps i k)) b) ||
                                  if SR.ps_pc (leafps i k) =? PARENT then act_eqb (dispatch st ST_ROOT b) a else all_parents (fun p => act_eqb (dispatch st p b) a))
      | _, _ => false
      end
  | Some (st, None, a) => RLF.all_bytes (fun b => all_parents (fun p => act_eqb (dispatch st p b) a))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ncuts : nat := length G.CPS.
Definition nleaves (i : nat) : nat := length (CC.cp_PSS (getc i)).
(* [comment removed for export] *)
Definition ACT2 : list (option (Z * option nat * act)) := Eval vm_compute in (map (leaf_act I_HLO) (seq 0 (nleaves I_HLO))).
Definition ACT3 : list (option (Z * option nat * act)) := Eval vm_compute in (map (leaf_act I_HHI) (seq 0 (nleaves I_HHI))).
Definition lact (i k : nat) : option (Z * option nat * act) :=
  if Nat.eqb i I_HLO then nth k ACT2 None else if Nat.eqb i I_HHI then nth k ACT3 None else None.
(* [comment removed for export] *)
Definition ract (j : nat) : option act := match ret_src j with Some (i, k, _) => match lact i k with Some (_, _, a) => Some a | None => None end | None => None end.
Definition RACT : list (option act) := Eval vm_compute in (map ract (seq 0 ncuts)).
(* [comment removed for export] *)
Definition consumes (a : act) : bool :=
  match a with
  | AErr _ k => k | AAccept => false | ASkip => false | ASlash => true | ABegin _ => true | AEnd _ => true | AString _ => true | ANumber => true
  | ALit _ => false | AComma => true | AGoto _ k => k | APop k => k | APushCr => true | ALitDone => true | AParseString => false | AParseNumber => false | AStuck => false
  end.
Definition off_of (i : nat) : Z :=
  if Nat.eqb i I_L2 then 1 else
  match nth i RACT None, pcell 200 8 (CC.cp_know (getc i)), pcell 200 8 (CC.cp_know (getc I_HLO)) with
  | Some a, Some wp, Some wp0 => if consumes a && expr_eqb wp wp0 then 1 else 0
  | _, _, _ => 0
  end.
Definition OFFT : list Z := Eval vm_compute in (map off_of (seq 0 ncuts)).
Definition OFF (i : nat) : Z := nth i OFFT 0.

(* [comment removed for export] *)
Definition leaf_b0 (i k : nat) : option Z := match leaf_byte i k with Some (_, bv) => first_adm bv (SR.ps_cells (leafps i k)) 0 256 | None => None end.
Definition ppar_src (i k : nat) (snd : bool) : option (Z * Z * bool) := match leaf_st i k, leaf_b0 i k with Some st, Some b => Some (st, b, snd) | _, _ => None end.
Definition ppar_of (i : nat) : option (Z * Z * bool) :=
  match ret_src i with
  | Some (i0, k0, _) => match kind_of i0 with
                       | KParent => match ret_src i0 with Some (i1, k1, _) => ppar_src i1 k1 true | None => None end
                       | _ => ppar_src i0 k0 false
                       end
  | None => None end.
Definition PPART : list (option (Z * Z * bool)) := Eval vm_compute in (map (fun i => match kind_of i with KParent => ppar_of i | _ => None end) (seq 0 ncuts)).
Definition PPAR (i : nat) : option (Z * Z * bool) := nth i PPART None.
Lemma PPART_eq : PPART = map (fun i => match kind_of i with KParent => ppar_of i | _ => None end) (seq 0 ncuts). Proof. vm_compute. reflexivity. Qed.
(* [comment removed for export] *)
Definition A0 (i : nat) : expr := nth 10 (CC.cp_regs (getc i)) (ELit 0).

(* [comment removed for export] *)
Definition tabs_ok : bool :=
  forallb (fun k => leaf_act_chk I_HLO k) (seq 0 (nleaves I_HLO)) && forallb (fun k => leaf_act_chk I_HHI k) (seq 0 (nleaves I_HHI)).
Lemma tabs_ok_true : tabs_ok = true.
Proof. vm_compute. reflexivity. Qed.
Lemma ACT2_eq : ACT2 = map (leaf_act I_HLO) (seq 0 (nleaves I_HLO)). Proof. vm_compute. reflexivity. Qed.
Lemma ACT3_eq : ACT3 = map (leaf_act I_HHI) (seq 0 (nleaves I_HHI)). Proof. vm_compute. reflexivity. Qed.
Lemma RACT_eq : RACT = map ract (seq 0 ncuts). Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition census : list (option (Z * option nat * act)) * list (option (Z * option nat * act)) * list (option act) * list Z * list (option (Z * Z * bool)) := (ACT2, ACT3, RACT, OFFT, PPART).
End PSCW.
