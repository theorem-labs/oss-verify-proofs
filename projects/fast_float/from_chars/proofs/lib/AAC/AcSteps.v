(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec ShapeSet RealizesCfg AsanAcct PlacementCount AllocNodesCfg.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFacts FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxPlan FxFrame FxDrv FxRgs FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChTwoC.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcMrg AcCarve AcHand.

Module AcP0gen.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxSubst FxEnt FxCall FxFacts.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.AcShift.
Import ListNotations.
Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition rk (r : Z) : positive := bv_key (Z_to_bv 5 r).
(* [comment removed for export] *)
Fixpoint pins (x : positive) (l : list positive) : list positive :=
  match l with [] => [x] | y :: l' => if Pos.ltb x y then x :: l else if Pos.eqb x y then l else y :: pins x l' end.
Definition cl_lin (l : lin) (acc : list positive) : list positive := List.fold_left (fun a p => pins (fst p) a) (l_t l) acc.
Definition cl_bval (v : bval) (acc : list positive) : list positive := match v with BK _ => acc | BV l _ => cl_lin l acc end.
Definition cl_rg (R : region) (acc : list positive) : list positive :=
  List.fold_left (fun a p => cl_bval (snd p) a) (telems (rg_cont R)) (cl_lin (rg_size R) (cl_lin (rg_base R) acc)).
Definition fact_lins (f : fact) : list lin :=
  match f with
  | FCond _ a b _ => [a; b] | FRange l _ _ | FMod l _ _ | FBits l _ _ => [l] | FByte x v _ => [x; v]
  | FBytes x bs => x :: List.map fst bs
  end.
Definition memb (x : positive) (l : list positive) : bool := existsb (Pos.eqb x) l.
Definition fact_in (vs : list positive) (f : fact) : bool :=
  forallb (fun l => forallb (fun p => memb (fst p) vs) (l_t l)) (fact_lins f).

(* [comment removed for export] *)
Fixpoint ren_acc (vs : list positive) (i : nat) (t : tree lin) : tree lin :=
  match vs with [] => t | x :: vs' => ren_acc vs' (Datatypes.S i) (tset x (lvar (Pos.of_nat (32 + i))) t) end.
Definition ren_of (vs : list positive) : tree lin := ren_acc vs O TEmpty.
Definition rename_rg (ren : tree lin) (R : region) : region :=
  RG (lsubst ren (rg_base R)) (lsubst ren (rg_size R)) (rg_kind R) (tmap (bsubst ren) (rg_cont R)).
Definition p0_regs (regs : tree lin) : tree lin :=
  List.fold_left (fun t k => let l := rget regs (rk k) in
                             tset (rk k) (match is_const l with Some _ => l | None => lvar (Pos.of_nat (Z.to_nat k)) end) t)
    (List.map Z.of_nat (seq 1 31)) TEmpty.

(* [comment removed for export] *)
Definition win_rgs (ws : list (Z * Z)) : list region := List.map (fun p => RG (laddc (lvar 2) (fst p)) (lconst (snd p)) RW TEmpty) ws.
(* [comment removed for export] *)
Definition WIN_MAL : list (Z * Z) := [(-8192, 3872); (-4320, 2048); (-2272, 64); (-2208, 80); (-2128, 8); (-2120, 8); (-2112, 240); (-1872, 1816); (-56, 56)].
Definition p0_of (S : sst) (ws : list (Z * Z)) (sel : list nat) (splo sphi : Z) : sst * list positive :=
  let rgs := List.map (fun i => nth i (s_rgs S) (RG lc0 lc0 RW TEmpty)) sel in
  let vs := List.fold_left (fun a R => cl_rg R a) rgs [] in
  let ren := ren_of vs in
  (SST (s_pc S) (p0_regs (s_regs S)) (win_rgs ws ++ List.map (rename_rg ren) rgs)
       (FMod (lvar 2) 4 0 :: FRange (lvar 2) splo sphi :: List.map (fsubst ren) (List.filter (fact_in vs) (s_facts S)))
       (Pos.of_nat (32 + length vs)) RNone, vs).

(* [comment removed for export] *)
Fixpoint sig_geo (n : positive) (vs : list positive) (i : nat) (t : tree lin) : tree lin :=
  match vs with [] => t | x :: vs' => sig_geo n vs' (Datatypes.S i) (tset (n + Pos.of_nat (32 + i))%positive (lvar x) t) end.
Definition sig_of (n : positive) (regs : tree lin) (vs : list positive) : tree lin :=
  sig_geo n vs O (List.fold_left (fun t k => let l := rget regs (rk k) in
                                    match is_const l with Some _ => t | None => tset (n + Pos.of_nat (Z.to_nat k))%positive l t end)
                    (List.map Z.of_nat (seq 1 31)) TEmpty).
End AcP0gen.

Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition tempty_b (t : tree bval) : bool := match t with TEmpty => true | _ => false end.
Lemma tempty_b_eq : forall t, tempty_b t = true -> t = TEmpty. Proof. intros [|l v r] H; [reflexivity | discriminate]. Qed.
Definition rkind_eqb (a b : rkind) : bool := match a, b with RW, RW | RO, RO | RZ, RZ | RI, RI | RT, RT => true | _, _ => false end.
Lemma rkind_eqb_eq : forall a b, rkind_eqb a b = true -> a = b. Proof. intros [] [] H; try discriminate; reflexivity. Qed.

Inductive rstep : Type :=
| RSplit (i : nat) (R1 R2 : region) (o : Z)     (* [comment removed for export] *)
| RDrop (i : nat)                              (* [comment removed for export] *)
| RRebase (i : nat) (x b' : lin)               (* [comment removed for export] *)
| RMerge (i : nat)                             (* [comment removed for export] *)
| RMergeC (i : nat)                            (* [comment removed for export] *)
| RMergeCC (i : nat).                          (* [comment removed for export] *)

(* [comment removed for export] *)
Definition tshift (c : tree bval) (d : Z) : tree bval :=
  List.fold_left (fun acc p => tset (Z.to_pos (Zpos (fst p) + d)) (snd p) acc) (telems c) TEmpty.
(* [comment removed for export] *)
Definition tmerge (c1 c2 : tree bval) (d : Z) : tree bval :=
  List.fold_left (fun acc p => tset (Z.to_pos (Zpos (fst p) + d)) (snd p) acc) (telems c2) c1.

Definition csplit (l : list region) (i : nat) (ins : list region) : list region := firstn i l ++ ins ++ skipn (Datatypes.S i) l.

(* [comment removed for export] *)
Definition nsh_ok (fs : list fact) (r : Z * Z) (b : lin) (z : Z) : bool :=
  if (Z.leb SH_HI (fst r) || Z.leb (snd r + z) SH_LO)%bool then true else twoc_ns fs b z.
Definition step_rgs (n : positive) (fs : list fact) (l : list region) (st : rstep) : option (list region) :=
  match st with
  | RSplit i R1 R2 o =>
      match nth_error l i with
      | Some R => match is_const (rg_size R) with
                  | Some z => if (Z.ltb 0 o && Z.ltb o z && rg_sub_ok R R1 0 && rg_sub_ok R R2 o && Z.eqb (csz R1) o && Z.eqb (csz R2) (z - o) &&
                                  lin_eqb (rg_size R) (lconst z))%bool
                              then Some (csplit l i [R1; R2]) else None
                  | None => None
                  end
      | None => None
      end
  | RDrop i => match nth_error l i with Some R => Some (csplit l i [empty_rg R]) | None => None end
  | RRebase i x b' =>
      match nth_error l i with
      | Some R => match lin_off (rg_base R) x with
                  | Some c => if (existsb (fact_eqb (FCond BC_EQ x b' true)) fs && lin_eqb (rg_base R) (laddc x c) && lwf n b')%bool
                              then Some (csplit l i [RG (laddc b' c) (rg_size R) (rg_kind R) (rg_cont R)]) else None
                  | None => None
                  end
      | None => None
      end
  | RMerge i =>
      match nth_error l i with
      | Some R1 => match nth_error l (Datatypes.S i) with
        | Some R2 =>
          match is_const (rg_size R1), is_const (rg_size R2), lin_off (rg_base R2) (rg_base R1) with
          | Some z1, Some z2, Some d =>
              if (rkind_eqb (rg_kind R1) RW && rkind_eqb (rg_kind R2) RW && tempty_b (rg_cont R1) && tempty_b (rg_cont R2) &&
                  Z.eqb d z1 && Z.ltb 0 z1 && Z.ltb 0 z2 && lin_eqb (rg_size R1) (lconst z1) && lin_eqb (rg_size R2) (lconst z2) &&
                  Z.ltb (snd (irange fs (rg_base R1)) + z1 + z2) two64 &&
                  nsh_ok fs (irange fs (rg_base R1)) (rg_base R1) (z1 + z2))%bool
              then Some (firstn i l ++ RG (rg_base R1) (lconst (z1 + z2)) RW TEmpty :: skipn (Datatypes.S (Datatypes.S i)) l) else None
          | _, _, _ => None
          end
        | None => None
        end
      | None => None
      end
  | RMergeC i =>
      match nth_error l i with
      | Some R1 => match nth_error l (Datatypes.S i) with
        | Some R2 =>
          match is_const (rg_size R1), is_const (rg_size R2), lin_off (rg_base R2) (rg_base R1) with
          | Some z1, Some z2, Some d =>
              let c := tshift (rg_cont R2) z1 in
              if (rkind_eqb (rg_kind R1) RW && rkind_eqb (rg_kind R2) RW && tempty_b (rg_cont R1) &&
                  Z.eqb d z1 && Z.ltb 0 z1 && Z.ltb 0 z2 && lin_eqb (rg_size R1) (lconst z1) && lin_eqb (rg_size R2) (lconst z2) &&
                  Z.ltb (snd (irange fs (rg_base R1)) + z1 + z2) two64 &&
                  nsh_ok fs (irange fs (rg_base R1)) (rg_base R1) (z1 + z2) && mc_ok (rg_cont R2) c z1 z2)%bool
              then Some (firstn i l ++ RG (rg_base R1) (lconst (z1 + z2)) RW c :: skipn (Datatypes.S (Datatypes.S i)) l) else None
          | _, _, _ => None
          end
        | None => None
        end
      | None => None
      end
  | RMergeCC i =>
      match nth_error l i with
      | Some R1 => match nth_error l (Datatypes.S i) with
        | Some R2 =>
          match is_const (rg_size R1), is_const (rg_size R2), lin_off (rg_base R2) (rg_base R1) with
          | Some z1, Some z2, Some d =>
              let c := tmerge (rg_cont R1) (rg_cont R2) z1 in
              if (rkind_eqb (rg_kind R1) RW && rkind_eqb (rg_kind R2) RW && 
                  Z.eqb d z1 && Z.ltb 0 z1 && Z.ltb 0 z2 && lin_eqb (rg_size R1) (lconst z1) && lin_eqb (rg_size R2) (lconst z2) &&
                  Z.ltb (snd (irange fs (rg_base R1)) + z1 + z2) two64 &&
                  nsh_ok fs (irange fs (rg_base R1)) (rg_base R1) (z1 + z2) && mc2_ok (rg_cont R1) (rg_cont R2) c z1 z2)%bool
              then Some (firstn i l ++ RG (rg_base R1) (lconst (z1 + z2)) RW c :: skipn (Datatypes.S (Datatypes.S i)) l) else None
          | _, _, _ => None
          end
        | None => None
        end
      | None => None
      end
  end.
Fixpoint steps_rgs_ref (n : positive) (fs : list fact) (l : list region) (sts : list rstep) : option (list region) :=
  match sts with [] => Some l | st :: sts' => match step_rgs n fs l st with Some l' => steps_rgs_ref n fs l' sts' | None => None end end.
(* [comment removed for export] *)
Definition step_base (l : list region) (st : rstep) : option lin :=
  match st with
  | RMerge i | RMergeC i | RMergeCC i => match nth_error l i with Some R1 => Some (rg_base R1) | None => None end
  | _ => None
  end.
Definition step_rgs_r (r : Z * Z) (n : positive) (fs : list fact) (l : list region) (st : rstep) : option (list region) :=
  match st with
  | RMerge i =>
      match nth_error l i with
      | Some R1 => match nth_error l (Datatypes.S i) with
        | Some R2 =>
          match is_const (rg_size R1), is_const (rg_size R2), lin_off (rg_base R2) (rg_base R1) with
          | Some z1, Some z2, Some d =>
              if (rkind_eqb (rg_kind R1) RW && rkind_eqb (rg_kind R2) RW && tempty_b (rg_cont R1) && tempty_b (rg_cont R2) &&
                  Z.eqb d z1 && Z.ltb 0 z1 && Z.ltb 0 z2 && lin_eqb (rg_size R1) (lconst z1) && lin_eqb (rg_size R2) (lconst z2) &&
                  Z.ltb (snd r + z1 + z2) two64 &&
                  nsh_ok fs r (rg_base R1) (z1 + z2))%bool
              then Some (firstn i l ++ RG (rg_base R1) (lconst (z1 + z2)) RW TEmpty :: skipn (Datatypes.S (Datatypes.S i)) l) else None
          | _, _, _ => None
          end
        | None => None
        end
      | None => None
      end
  | RMergeC i =>
      match nth_error l i with
      | Some R1 => match nth_error l (Datatypes.S i) with
        | Some R2 =>
          match is_const (rg_size R1), is_const (rg_size R2), lin_off (rg_base R2) (rg_base R1) with
          | Some z1, Some z2, Some d =>
              let c := tshift (rg_cont R2) z1 in
              if (rkind_eqb (rg_kind R1) RW && rkind_eqb (rg_kind R2) RW && tempty_b (rg_cont R1) &&
                  Z.eqb d z1 && Z.ltb 0 z1 && Z.ltb 0 z2 && lin_eqb (rg_size R1) (lconst z1) && lin_eqb (rg_size R2) (lconst z2) &&
                  Z.ltb (snd r + z1 + z2) two64 &&
                  nsh_ok fs r (rg_base R1) (z1 + z2) && mc_ok (rg_cont R2) c z1 z2)%bool
              then Some (firstn i l ++ RG (rg_base R1) (lconst (z1 + z2)) RW c :: skipn (Datatypes.S (Datatypes.S i)) l) else None
          | _, _, _ => None
          end
        | None => None
        end
      | None => None
      end
  | RMergeCC i =>
      match nth_error l i with
      | Some R1 => match nth_error l (Datatypes.S i) with
        | Some R2 =>
          match is_const (rg_size R1), is_const (rg_size R2), lin_off (rg_base R2) (rg_base R1) with
          | Some z1, Some z2, Some d =>
              let c := tmerge (rg_cont R1) (rg_cont R2) z1 in
              if (rkind_eqb (rg_kind R1) RW && rkind_eqb (rg_kind R2) RW && 
                  Z.eqb d z1 && Z.ltb 0 z1 && Z.ltb 0 z2 && lin_eqb (rg_size R1) (lconst z1) && lin_eqb (rg_size R2) (lconst z2) &&
                  Z.ltb (snd r + z1 + z2) two64 &&
                  nsh_ok fs r (rg_base R1) (z1 + z2) && mc2_ok (rg_cont R1) (rg_cont R2) c z1 z2)%bool
              then Some (firstn i l ++ RG (rg_base R1) (lconst (z1 + z2)) RW c :: skipn (Datatypes.S (Datatypes.S i)) l) else None
          | _, _, _ => None
          end
        | None => None
        end
      | None => None
      end
  | _ => step_rgs n fs l st
  end.
Lemma step_rgs_r_eq : forall n fs l st b, step_base l st = Some b -> step_rgs_r (irange fs b) n fs l st = step_rgs n fs l st.
Proof.
  intros n fs l st b H. destruct st as [i R1 R2 o|i|i x b'|i|i|i]; cbn [step_base] in H; try discriminate;
    unfold step_rgs_r, step_rgs; destruct (nth_error l i) as [R1|]; try discriminate; injection H as <-; reflexivity.
Qed.
Fixpoint steps_rgs_c (ch : option (lin * (Z * Z))) (n : positive) (fs : list fact) (l : list region) (sts : list rstep) : option (list region) :=
  match sts with
  | [] => Some l
  | st :: sts' =>
      match step_base l st with
      | Some b =>
          let r := match ch with Some (b0, r0) => if lin_eqb b0 b then r0 else irange fs b | None => irange fs b end in
          match step_rgs_r r n fs l st with Some l' => steps_rgs_c (Some (b, r)) n fs l' sts' | None => None end
      | None => match step_rgs n fs l st with Some l' => steps_rgs_c ch n fs l' sts' | None => None end
      end
  end.
Definition steps_rgs (n : positive) (fs : list fact) (l : list region) (sts : list rstep) : option (list region) := steps_rgs_c None n fs l sts.
Lemma steps_rgs_c_eq : forall sts ch n fs l, (forall b r, ch = Some (b, r) -> r = irange fs b) ->
  steps_rgs_c ch n fs l sts = steps_rgs_ref n fs l sts.
Proof.
  induction sts as [|st sts IH]; intros ch n fs l Hch; cbn [steps_rgs_c steps_rgs_ref]; [reflexivity|].
  destruct (step_base l st) as [b|] eqn:Hb.
  - cbv zeta.
    assert (Hr : match ch with Some (b0, r0) => if lin_eqb b0 b then r0 else irange fs b | None => irange fs b end = irange fs b).
    { destruct ch as [[b0 r0]|]; [|reflexivity]. destruct (lin_eqb b0 b) eqn:Hq; [|reflexivity].
      apply lin_eqb_eq in Hq. subst b0. exact (Hch b r0 eq_refl). }
    rewrite Hr, (step_rgs_r_eq n fs l st b Hb). destruct (step_rgs n fs l st) as [l'|]; [|reflexivity].
    apply IH. intros b1 r1 H1. injection H1 as <- <-. reflexivity.
  - destruct (step_rgs n fs l st) as [l'|]; [|reflexivity]. exact (IH ch n fs l' Hch).
Qed.
Lemma steps_rgs_eq : forall n fs l sts, steps_rgs n fs l sts = steps_rgs_ref n fs l sts.
Proof. intros. unfold steps_rgs. apply steps_rgs_c_eq. intros b r H. discriminate. Qed.
Lemma steps_rgs_nil : forall n fs l, steps_rgs n fs l [] = Some l.
Proof. reflexivity. Qed.
Lemma steps_rgs_cons : forall n fs l st sts,
  steps_rgs n fs l (st :: sts) = match step_rgs n fs l st with Some l' => steps_rgs n fs l' sts | None => None end.
Proof.
  intros. rewrite steps_rgs_eq. cbn [steps_rgs_ref]. destruct (step_rgs n fs l st) as [l'|]; [|reflexivity]. symmetry. apply steps_rgs_eq.
Qed.

Lemma nth_split : forall {A} (l : list A) i x, nth_error l i = Some x -> l = firstn i l ++ x :: skipn (Datatypes.S i) l.
Proof.
  intros A l. induction l as [|y l IH]; intros i x H; [destruct i; discriminate|]. destruct i as [|i]; cbn in H |- *.
  - injection H as <-. reflexivity.
  - f_equal. exact (IH i x H).
Qed.
Lemma nth_split2 : forall {A} (l : list A) i x y, nth_error l i = Some x -> nth_error l (Datatypes.S i) = Some y ->
  l = firstn i l ++ x :: y :: skipn (Datatypes.S (Datatypes.S i)) l.
Proof.
  intros A l. induction l as [|z l IH]; intros i x y H1 H2; [destruct i; discriminate|]. destruct i as [|i]; cbn in H1, H2 |- *.
  - injection H1 as <-. destruct l as [|w l]; [discriminate|]. cbn in H2. injection H2 as <-. reflexivity.
  - f_equal. exact (IH i x y H1 H2).
Qed.

Lemma rg_ok_empty : forall segs E m R, rg_ok segs E m R -> rg_ok segs E m (empty_rg R).
Proof.
  intros segs E m R HR. destruct HR as (H1 & H2 & H3 & _). unfold rg_ok, empty_rg. cbv zeta. unfold rsz in *. cbn [rg_base rg_size rg_kind rg_cont].
  refine (conj H1 (conj H2 (conj _ _))).
  - intros i Hi. specialize (H3 i Hi). destruct (rg_kind R); try exact H3; exact (proj1 H3).
  - intros p v Hp. rewrite tget_empty in Hp. discriminate.
Qed.

Section Steps.
Variable segs : list Segment.
Variable LIMIT : Z.
Variable model0 : Model.
Variable mem0 : word -> option byte.

#[using="Type"] Theorem den_step : forall E S M ms model st l',
  DEN segs LIMIT model0 mem0 E S M ms model -> step_rgs (s_next S) (s_facts S) (s_rgs S) st = Some l' ->
  DEN segs LIMIT model0 mem0 E (with_rgs S l') M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E S M ms model st l' Hd Hst.
  assert (HF : forall E', agree (s_next S) E E' -> Forall (fact_ok E') (s_facts S)).
  { intros E' Ha. destruct (dn_sden _ _ _ _ _ _ _ _ _ Hd E' Ha) as (_ & _ & _ & _ & _ & _ & X & _). exact X. }
  destruct st as [i R1 R2 o|i|i x b'|i|i|i]; cbn [step_rgs] in Hst.
  - destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. destruct (is_const (rg_size R)) as [z|] eqn:Hz; [|discriminate].
    destruct (Z.ltb 0 o && Z.ltb o z && rg_sub_ok R R1 0 && rg_sub_ok R R2 o && Z.eqb (csz R1) o && Z.eqb (csz R2) (z - o) &&
              lin_eqb (rg_size R) (lconst z))%bool eqn:Hb; [|discriminate]. injection Hst as <-.
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
    repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end.
    match goal with H : lin_eqb (rg_size R) (lconst z) = true |- _ => apply lin_eqb_eq in H end.
    destruct (is_const_sound E _ z Hz) as [_ Hzr].
    apply (den_split segs LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) R (skipn (Datatypes.S i) (s_rgs S)) R1 R2 o z Hd
             (nth_split _ i R Hi)); assumption || (unfold two64 in *; lia).
  - destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. injection Hst as <-.
    apply (den_weaken_rg segs LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) R (skipn (Datatypes.S i) (s_rgs S)) (empty_rg R) Hd
             (nth_split _ i R Hi) eq_refl eq_refl).
    intros E' m _ HR. exact (rg_ok_empty segs E' m R HR).
  - destruct (nth_error (s_rgs S) i) as [R|] eqn:Hi; [|discriminate]. destruct (lin_off (rg_base R) x) as [c|] eqn:Hc; [|discriminate].
    destruct (existsb (fact_eqb (FCond BC_EQ x b' true)) (s_facts S) && lin_eqb (rg_base R) (laddc x c) && lwf (s_next S) b')%bool eqn:Hb; [|discriminate].
    injection Hst as <-. apply andb_prop in Hb as [Hb Hw]. apply andb_prop in Hb as [Hf Hbx]. apply lin_eqb_eq in Hbx.
    apply existsb_exists in Hf as (f & Hfin & Hfe). apply fact_eqb_eq in Hfe. subst f.
    apply (den_rebase segs LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) R (skipn (Datatypes.S i) (s_rgs S)) (laddc b' c) Hd
             (nth_split _ i R Hi)).
    + unfold lwf in *. cbn [laddc l_t]. exact Hw.
    + intros E' Ha. pose proof (HF E' Ha) as HF'. rewrite Forall_forall in HF'. pose proof (fact_eq_sound E' _ _ (HF' _ Hfin)) as Heq.
      rewrite Hbx, !lden_laddc, Heq. reflexivity.
  - destruct (nth_error (s_rgs S) i) as [R1|] eqn:Hi1; [|discriminate]. destruct (nth_error (s_rgs S) (Datatypes.S i)) as [R2|] eqn:Hi2; [|discriminate].
    destruct (is_const (rg_size R1)) as [z1|] eqn:Hs1; [|discriminate]. destruct (is_const (rg_size R2)) as [z2|] eqn:Hs2; [|discriminate].
    destruct (lin_off (rg_base R2) (rg_base R1)) as [d|] eqn:Hd12; [|discriminate].
    destruct (rkind_eqb (rg_kind R1) RW && rkind_eqb (rg_kind R2) RW && tempty_b (rg_cont R1) && tempty_b (rg_cont R2) &&
              Z.eqb d z1 && Z.ltb 0 z1 && Z.ltb 0 z2 && lin_eqb (rg_size R1) (lconst z1) && lin_eqb (rg_size R2) (lconst z2) &&
              Z.ltb (snd (irange (s_facts S) (rg_base R1)) + z1 + z2) two64 &&
              nsh_ok (s_facts S) (irange (s_facts S) (rg_base R1)) (rg_base R1) (z1 + z2))%bool eqn:Hb; [|discriminate].
    destruct R1 as [b1 s1 k1 c1]. destruct R2 as [b2 s2 k2 c2]. cbn [rg_base rg_size rg_kind rg_cont] in *.
    injection Hst as <-.
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
    repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end.
    repeat match goal with H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H | H : rkind_eqb _ _ = true |- _ => apply rkind_eqb_eq in H
                        | H : tempty_b _ = true |- _ => apply tempty_b_eq in H end. subst s1 s2 d k1 k2 c1 c2.
    match goal with H : nsh_ok _ _ _ _ = true |- _ => rename H into Hsh end.
    pose proof (nth_split2 _ i _ _ Hi1 Hi2) as HS.
    assert (HR : forall E', agree (s_next S) E E' -> fst (irange (s_facts S) b1) <= uE E' b1 <= snd (irange (s_facts S) b1)).
    { intros E' Ha. exact (irange_sound E' _ b1 (HF E' Ha)). }
    pose proof (HR E (agree_refl _ _)) as HR0. pose proof (bv_unsigned_in_range _ (lden E b1)) as HU0. unfold uE in HR0.
    apply (den_merge0 segs LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) b1 b2 z1 z2 (skipn (Datatypes.S (Datatypes.S i)) (s_rgs S)) Hd HS);
      try (unfold two64 in *; lia).
    + intros E' Ha. destruct (lin_off_sound E' b2 b1 z1 Hd12) as [Hl Hr]. rewrite lden_lsub in Hl. pose proof (HR E' Ha) as Rb.
      unfold uE in *. assert (X : lden E' b2 = (Z_to_bv 64 z1 + lden E' b1)%bv).
      { rewrite <- Hl. apply bv_eq. rewrite !bv_add_unsigned, bv_sub_unsigned. unfold bv_wrap, bv_modulus. rewrite Zplus_mod_idemp_l.
        replace (bv_unsigned (lden E' b2) - bv_unsigned (lden E' b1) + bv_unsigned (lden E' b1)) with (bv_unsigned (lden E' b2)) by lia.
        symmetry. apply Z.mod_small. apply bv_unsigned_in_range. }
      rewrite X, bv_add_unsigned, u_small64 by exact Hr. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.add_comm. apply Z.mod_small. pose proof (bv_unsigned_in_range _ (lden E' b1)). lia.
    + intros w Hw. pose proof (HR E (agree_refl _ _)) as Rb. unfold in_shadow. apply andb_false_iff.
      unfold nsh_ok in Hsh. cbn [rg_base] in Hsh.
      match type of Hsh with (if ?c then _ else _) = _ => destruct c eqn:Hor end.
      * apply orb_prop in Hor as [Hor|Hor]; apply Z.leb_le in Hor; [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia.
      * (* [comment removed for export] *)
        apply (proj1 (andb_false_iff _ _)). exact (twoc_ns_noshadow E (s_facts S) b1 (z1 + z2) (HF E (agree_refl _ _)) Hsh ltac:(lia) w ltac:(unfold uE in *; lia)).
  - destruct (nth_error (s_rgs S) i) as [R1|] eqn:Hi1; [|discriminate]. destruct (nth_error (s_rgs S) (Datatypes.S i)) as [R2|] eqn:Hi2; [|discriminate].
    destruct (is_const (rg_size R1)) as [z1|] eqn:Hs1; [|discriminate]. destruct (is_const (rg_size R2)) as [z2|] eqn:Hs2; [|discriminate].
    destruct (lin_off (rg_base R2) (rg_base R1)) as [d|] eqn:Hd12; [|discriminate]. cbv zeta in Hst.
    destruct (rkind_eqb (rg_kind R1) RW && rkind_eqb (rg_kind R2) RW && tempty_b (rg_cont R1) &&
              Z.eqb d z1 && Z.ltb 0 z1 && Z.ltb 0 z2 && lin_eqb (rg_size R1) (lconst z1) && lin_eqb (rg_size R2) (lconst z2) &&
              Z.ltb (snd (irange (s_facts S) (rg_base R1)) + z1 + z2) two64 &&
              nsh_ok (s_facts S) (irange (s_facts S) (rg_base R1)) (rg_base R1) (z1 + z2) &&
              mc_ok (rg_cont R2) (tshift (rg_cont R2) z1) z1 z2)%bool eqn:Hb; [|discriminate].
    destruct R1 as [b1 s1 k1 c1]. destruct R2 as [b2 s2 k2 c2]. cbn [rg_base rg_size rg_kind rg_cont] in *.
    injection Hst as <-.
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
    repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end.
    repeat match goal with H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H | H : rkind_eqb _ _ = true |- _ => apply rkind_eqb_eq in H
                        | H : tempty_b _ = true |- _ => apply tempty_b_eq in H end. subst s1 s2 d k1 k2 c1.
    match goal with H : nsh_ok _ _ _ _ = true |- _ => rename H into Hsh end.
    pose proof (nth_split2 _ i _ _ Hi1 Hi2) as HS.
    assert (HR : forall E', agree (s_next S) E E' -> fst (irange (s_facts S) b1) <= uE E' b1 <= snd (irange (s_facts S) b1)).
    { intros E' Ha. exact (irange_sound E' _ b1 (HF E' Ha)). }
    pose proof (HR E (agree_refl _ _)) as HR0. pose proof (bv_unsigned_in_range _ (lden E b1)) as HU0. unfold uE in HR0.
    apply (den_mergeC segs LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) b1 b2 z1 z2 c2 (tshift c2 z1) (skipn (Datatypes.S (Datatypes.S i)) (s_rgs S)) Hd HS);
      try assumption; try (unfold two64 in *; lia).
    + intros E' Ha. destruct (lin_off_sound E' b2 b1 z1 Hd12) as [Hl Hr]. rewrite lden_lsub in Hl. pose proof (HR E' Ha) as Rb.
      unfold uE in *. assert (X : lden E' b2 = (Z_to_bv 64 z1 + lden E' b1)%bv).
      { rewrite <- Hl. apply bv_eq. rewrite !bv_add_unsigned, bv_sub_unsigned. unfold bv_wrap, bv_modulus. rewrite Zplus_mod_idemp_l.
        replace (bv_unsigned (lden E' b2) - bv_unsigned (lden E' b1) + bv_unsigned (lden E' b1)) with (bv_unsigned (lden E' b2)) by lia.
        symmetry. apply Z.mod_small. apply bv_unsigned_in_range. }
      rewrite X, bv_add_unsigned, u_small64 by exact Hr. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.add_comm. apply Z.mod_small. pose proof (bv_unsigned_in_range _ (lden E' b1)). lia.
    + intros w Hw. pose proof (HR E (agree_refl _ _)) as Rb. unfold in_shadow. apply andb_false_iff.
      unfold nsh_ok in Hsh. cbn [rg_base] in Hsh.
      match type of Hsh with (if ?c then _ else _) = _ => destruct c eqn:Hor end.
      * apply orb_prop in Hor as [Hor|Hor]; apply Z.leb_le in Hor; [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia.
      * (* [comment removed for export] *)
        apply (proj1 (andb_false_iff _ _)). exact (twoc_ns_noshadow E (s_facts S) b1 (z1 + z2) (HF E (agree_refl _ _)) Hsh ltac:(lia) w ltac:(unfold uE in *; lia)).
  - destruct (nth_error (s_rgs S) i) as [R1|] eqn:Hi1; [|discriminate]. destruct (nth_error (s_rgs S) (Datatypes.S i)) as [R2|] eqn:Hi2; [|discriminate].
    destruct (is_const (rg_size R1)) as [z1|] eqn:Hs1; [|discriminate]. destruct (is_const (rg_size R2)) as [z2|] eqn:Hs2; [|discriminate].
    destruct (lin_off (rg_base R2) (rg_base R1)) as [d|] eqn:Hd12; [|discriminate]. cbv zeta in Hst.
    destruct (rkind_eqb (rg_kind R1) RW && rkind_eqb (rg_kind R2) RW &&
              Z.eqb d z1 && Z.ltb 0 z1 && Z.ltb 0 z2 && lin_eqb (rg_size R1) (lconst z1) && lin_eqb (rg_size R2) (lconst z2) &&
              Z.ltb (snd (irange (s_facts S) (rg_base R1)) + z1 + z2) two64 &&
              nsh_ok (s_facts S) (irange (s_facts S) (rg_base R1)) (rg_base R1) (z1 + z2) &&
              mc2_ok (rg_cont R1) (rg_cont R2) (tmerge (rg_cont R1) (rg_cont R2) z1) z1 z2)%bool eqn:Hb; [|discriminate].
    destruct R1 as [b1 s1 k1 c1]. destruct R2 as [b2 s2 k2 c2]. cbn [rg_base rg_size rg_kind rg_cont] in *.
    injection Hst as <-.
    repeat match goal with H : (_ && _)%bool = true |- _ => apply andb_prop in H as [? ?] end.
    repeat match goal with H : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in H | H : Z.ltb _ _ = true |- _ => apply Z.ltb_lt in H end.
    repeat match goal with H : lin_eqb _ _ = true |- _ => apply lin_eqb_eq in H | H : rkind_eqb _ _ = true |- _ => apply rkind_eqb_eq in H
                        | H : tempty_b _ = true |- _ => apply tempty_b_eq in H end. subst s1 s2 d k1 k2.
    match goal with H : nsh_ok _ _ _ _ = true |- _ => rename H into Hsh end.
    pose proof (nth_split2 _ i _ _ Hi1 Hi2) as HS.
    assert (HR : forall E', agree (s_next S) E E' -> fst (irange (s_facts S) b1) <= uE E' b1 <= snd (irange (s_facts S) b1)).
    { intros E' Ha. exact (irange_sound E' _ b1 (HF E' Ha)). }
    pose proof (HR E (agree_refl _ _)) as HR0. pose proof (bv_unsigned_in_range _ (lden E b1)) as HU0. unfold uE in HR0.
    apply (den_mergeCC segs LIMIT model0 mem0 E S M ms model (firstn i (s_rgs S)) b1 b2 z1 z2 c1 c2 (tmerge c1 c2 z1) (skipn (Datatypes.S (Datatypes.S i)) (s_rgs S)) Hd HS);
      try assumption; try (unfold two64 in *; lia).
    + intros E' Ha. destruct (lin_off_sound E' b2 b1 z1 Hd12) as [Hl Hr]. rewrite lden_lsub in Hl. pose proof (HR E' Ha) as Rb.
      unfold uE in *. assert (X : lden E' b2 = (Z_to_bv 64 z1 + lden E' b1)%bv).
      { rewrite <- Hl. apply bv_eq. rewrite !bv_add_unsigned, bv_sub_unsigned. unfold bv_wrap, bv_modulus. rewrite Zplus_mod_idemp_l.
        replace (bv_unsigned (lden E' b2) - bv_unsigned (lden E' b1) + bv_unsigned (lden E' b1)) with (bv_unsigned (lden E' b2)) by lia.
        symmetry. apply Z.mod_small. apply bv_unsigned_in_range. }
      rewrite X, bv_add_unsigned, u_small64 by exact Hr. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
      rewrite Z.add_comm. apply Z.mod_small. pose proof (bv_unsigned_in_range _ (lden E' b1)). lia.
    + intros w Hw. pose proof (HR E (agree_refl _ _)) as Rb. unfold in_shadow. apply andb_false_iff.
      unfold nsh_ok in Hsh. cbn [rg_base] in Hsh.
      match type of Hsh with (if ?c then _ else _) = _ => destruct c eqn:Hor end.
      * apply orb_prop in Hor as [Hor|Hor]; apply Z.leb_le in Hor; [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia.
      * (* [comment removed for export] *)
        apply (proj1 (andb_false_iff _ _)). exact (twoc_ns_noshadow E (s_facts S) b1 (z1 + z2) (HF E (agree_refl _ _)) Hsh ltac:(lia) w ltac:(unfold uE in *; lia)).
Qed.

#[using="Type"] Theorem den_steps : forall sts E S M ms model l',
  DEN segs LIMIT model0 mem0 E S M ms model -> steps_rgs (s_next S) (s_facts S) (s_rgs S) sts = Some l' ->
  DEN segs LIMIT model0 mem0 E (with_rgs S l') M ms model.
Proof. LiaFast.lf_pins LiaFast.u0.
  induction sts as [|st sts IH]; intros E S M ms model l' Hd Hst; [rewrite steps_rgs_nil in Hst | rewrite steps_rgs_cons in Hst].
  - injection Hst as <-. destruct S; exact Hd.
  - destruct (step_rgs (s_next S) (s_facts S) (s_rgs S) st) as [l1|] eqn:H1; [|discriminate].
    pose proof (den_step E S M ms model st l1 Hd H1) as Hd1.
    exact (IH E (with_rgs S l1) M ms model l' Hd1 Hst).
Qed.
End Steps.
