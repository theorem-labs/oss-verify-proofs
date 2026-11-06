(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith Lia Bool List.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.ct.lib.VCommon Require Import PropExec FastWord FastWordSem ShapeAlg ShapeAlgCfg.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import ExTrie.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxLazy AxLin AxVal AxMem AxState AxStep AxFetchFast AxDecFast AxSys AxJoinSound.
From OSSVerify.Proofs.openssl.ct.lib.VCommon.Ax Require Import AxModelRel.
Import ListNotations.

Local Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
Definition derive2 (T : lin) (H F : fact) : option (Z * Z) :=
  if fc_hole H &&& negb (fc_hole F) then
    let gp := ladd (fc_f H) (fc_f F) in
    if teqb (snd gp) (snd T) then Some (fc_lo H + fc_hi F + (fst T - fst gp), fc_hi H + fc_lo F + (fst T - fst gp)) else
    let gm := lsub (fc_f H) (fc_f F) in
    if teqb (snd gm) (snd T) then Some (fc_lo H - fc_lo F + (fst T - fst gm), fc_hi H - fc_hi F + (fst T - fst gm)) else None
  else None.

Lemma leval_same_terms (ρ : valuation) (T g : lin) : snd g = snd T -> leval ρ T = leval ρ g + (fst T - fst g).
Proof. intros E. unfold leval. rewrite E. ring. Qed.

Lemma derive2_sound (ρ : valuation) (T : lin) (H F : fact) (lo hi : Z) :
  fact_sat ρ H -> fact_sat ρ F -> derive2 T H F = Some (lo, hi) -> leval ρ T <= lo \/ hi <= leval ρ T.
Proof.
  intros HH HF E. unfold derive2 in E.
  destruct (fc_hole H) eqn:EH; [|discriminate E]. destruct (fc_hole F) eqn:EF; [discriminate E|]. cbn [negb] in E.
  unfold fact_sat in HH, HF. rewrite EH in HH. rewrite EF in HF.
  destruct (teqb (snd (ladd (fc_f H) (fc_f F))) (snd T)) eqn:Ep.
  - apply teqb_eq in Ep. injection E as <- <-. rewrite (leval_same_terms ρ T _ Ep), leval_ladd. unfold ladd. cbn [fst]. lia.
  - destruct (teqb (snd (lsub (fc_f H) (fc_f F))) (snd T)) eqn:Em; [|discriminate E].
    apply teqb_eq in Em. injection E as <- <-. rewrite (leval_same_terms ρ T _ Em), leval_lsub.
    unfold lsub, ladd, lscale. cbn [fst Z.eqb]. lia.
Qed.

(* [comment removed for export] *)
Fixpoint derive1 (T : lin) (H : fact) (fs : list fact) : option (Z * Z) :=
  match fs with
  | [] => None
  | F :: r => match derive2 T H F with Some p => Some p | None => derive1 T H r end
  end.

Fixpoint derive (T : lin) (hs fs : list fact) : option (Z * Z) :=
  match hs with
  | [] => None
  | H :: r => match (if fc_hole H then derive1 T H fs else None) with Some p => Some p | None => derive T r fs end
  end.

Lemma derive1_sound (ρ : valuation) (T : lin) (H : fact) (lo hi : Z) : forall fs,
  fact_sat ρ H -> Forall (fact_sat ρ) fs -> derive1 T H fs = Some (lo, hi) -> leval ρ T <= lo \/ hi <= leval ρ T.
Proof.
  induction fs as [|F r IH]; intros HH Hfs E; cbn [derive1] in E; [discriminate E|].
  inversion Hfs as [|? ? HF Hr]; subst.
  destruct (derive2 T H F) as [p|] eqn:E2; [injection E as ->; exact (derive2_sound ρ T H F lo hi HH HF E2) | exact (IH HH Hr E)].
Qed.

Lemma derive_sound (ρ : valuation) (T : lin) (lo hi : Z) (fs : list fact) : forall hs,
  Forall (fact_sat ρ) hs -> Forall (fact_sat ρ) fs -> derive T hs fs = Some (lo, hi) -> leval ρ T <= lo \/ hi <= leval ρ T.
Proof.
  induction hs as [|H r IH]; intros Hhs Hfs E; cbn [derive] in E; [discriminate E|].
  inversion Hhs as [|? ? HH Hr]; subst.
  destruct (if fc_hole H then derive1 T H fs else None) as [p|] eqn:E1; [|exact (IH Hr Hfs E)].
  injection E as ->. destruct (fc_hole H); [|discriminate E1]. exact (derive1_sound ρ T H lo hi fs HH Hfs E1).
Qed.

(* [comment removed for export] *)
Definition hole_target (segs : list Segment) (A : AST) : option lin :=
  match fetch_fast segs (a_pc A) with
  | Some w =>
      match DecodeC.decode_any w with
      | Some (i, _) =>
          match dec_fast i with
          | DBranch _ rs1 rs2 _ =>
              match xform (a_facts A) (aget (a_regs A) rs1), xform (a_facts A) (aget (a_regs A) rs2) with
              | Some f, Some g => Some (lsub f g)
              | _, _ => None
              end
          | _ => None
          end
      | None => None
      end
  | None => None
  end.

Definition tnil_b (ts : terms) : bool := match ts with [] => true | _ => false end.

Definition has_hole (fs : list fact) (ts : terms) : bool := lexists (fun F => fc_hole F &&& teqb (snd (fc_f F)) ts) fs.

Definition sum_holes (segs : list Segment) (A : AST) : option (list AST) :=
  match hole_target segs A with
  | Some T =>
      let s := a_facts A in
      if tnil_b (snd T) ||| has_hole (st_facts s) (snd T) then None else
      match derive T (st_facts s) (st_facts s) with
      | Some (lo, hi) => Some [AS (a_pc A) (a_regs A) (a_resv A) (a_mem A) (shole s T lo hi) (a_model A) (a_budget A) (a_steps A)]
      | None => None
      end
  | None => None
  end.

Section HoleSound.
Variable segs : list Segment.
Variable cfg : SpuriousCfg.
Variable LIM : Z.
Variable fs0 : Fs.Fs.
Variable KT : valuation -> list byte -> TSet.

Notation Snd := (Sound segs cfg LIM (MR segs fs0) KT).

Theorem sum_holes_sound (A : AST) (l : list AST) : sum_holes segs A = Some l -> (forall B, In B l -> Snd B) -> Snd A.
Proof.
  intros Hs HS ρ c HR o Ho. unfold sum_holes in Hs.
  destruct (hole_target segs A) as [T|]; [|discriminate Hs].
  destruct (tnil_b (snd T) ||| has_hole (st_facts (a_facts A)) (snd T)); [discriminate Hs|].
  destruct (derive T (st_facts (a_facts A)) (st_facts (a_facts A))) as [[lo hi]|] eqn:Ed; [|discriminate Hs].
  injection Hs as <-.
  refine (HS _ (or_introl eq_refl) ρ c _ o Ho).
  destruct HR as [Hpc Hal0 Hsvc Hregs Hres Hrom Hmem Hmod Hh Hb Hsat Hhs Hcov Hcomp Hnaok].
  constructor; cbn [a_pc a_regs a_resv a_mem a_facts a_model a_budget]; try assumption.
  apply sat_shole; [exact Hsat|]. destruct Hsat as [_ Hf]. exact (derive_sound ρ T lo hi _ _ Hf Hf Ed).
Qed.

End HoleSound.
