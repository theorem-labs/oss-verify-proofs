(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Datatypes"; "bool"; "list"; "nat"; "option"; "false"; "andb"; "prod"; "true"; "app"; "negb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "axst"; "leafA"; "ax_S"; "axwf"; "entailsA"; "la_state"; "sym_runA"; "xr_covered"; "xr_eqb"; "xr_sub"; "@Corelib.Init.Logic"; "eq"; "@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.CFGA"; "edgeA"; "check_cfgA"; "check_cutA"; "cuts_edgesA"; "first_matchA"; "leaf_matches1A"; "leaf_matchesA"; "leaf_okA"; "leaf_okA_ref"; "leaf_refuted"; "leaves_edgesA"; "leaves_edgesA_ref"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.RingCfg"; "rnode"; "node_okb"; "rcheck"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "ss_pc"; "sprop"; "ss_lenient"; "ss_next"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "wsub"; "wsub_id_below"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.FastChkA.F"; "leaf_okA'"; "check_cutA'"; "cuts_edgesA'"; "leaf_matches1A'"; "leaf_matchesA'"; "leaves_edgesA'"; "check_cfgA'"; "first_matchA'"; "@Corelib.Lists.ListDef"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymCFG"; "forallb_lazy"; "existsb_lazy"; "infer_sub"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.FastChkA"; "entailsA'"; "xr_covered'"; "@Stdlib.Lists.List"; "existsb"; "forallb"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.FastChkA.F.RC"; "check_rcfgA'"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.RingCfgA"; "check_rcfgA"; "e2e"; "rnA"; "srcA"; "@Stdlib.PArith.BinPos.Pos"; "leb"; "@Stdlib.ZArith.BinInt.Z"; "eqb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR
  SymComplete SymFrame SymEntail SymCFG.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA EntailA CompleteA CFGA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import RingBuf Ring RingCfg.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA Require Import RingCfgA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition xr_covered' (facts : list sprop) (X : list (sv * sv)) (r' : sv * sv) : bool := ltac2:(tb__ "0|1|
S0S0L_;S3bS6S26S26A2M0S12Vr';A1VX;A3S7S3bG0S13Vfacts;Vr';A2VX;A3X0x2").
Lemma xr_covered'_eq : ltac2:(tb__ "0|1|
S1S28A1S1S6S26S26A2M0A1G0S14S0S3aR3R2R1A3S11R3R2R1A3A3Fr';FX;Ffacts;").
Proof. intros. unfold xr_covered', xr_covered. destruct (existsb (xr_eqb r') X); reflexivity. Qed.

Definition entailsA' (L T : axst) (s : wsub) : bool := entailsA L T s.
Lemma entailsA'_eq : ltac2:(tb__ "0|0|
SaSaS2bS14S0S39R3R2R1A3SeR3R2R1A3A3Fs;FT;FL;").
Proof. reflexivity. Qed.

Section F.
Variable segs : list Segment.

Definition leaf_matches1A' (g : positive) (L X : axst) : bool := ltac2:(tb__ "0|3|
S0S0L_;M0S43S27ScVL;A1M1A1S27ScVX;A1M2A1A2S38Vg;G1G2A3S2bG0S2cR1Vg;A2S39VL;VX;R1A3S4X0x2Ts;S4X0x2").
Lemma leaf_matches1A'_eq : ltac2:(tb__ "0|0|
S15SaSaS14S0S30R3R2R1A3S1cR3R2R1A3A3FX;FL;Fg;").
Proof. intros. unfold leaf_matches1A', leaf_matches1A. rewrite entailsA'_eq. reflexivity. Qed.

Lemma existsb_lazy_ext : forall {A} (f h : A -> bool) l, (forall x, f x = h x) -> existsb_lazy f l = existsb_lazy h l.
Proof. intros A f h l H. induction l as [|x t IH]; cbn; [reflexivity|]. rewrite H, IH. reflexivity. Qed.
Lemma forallb_lazy_ext : forall {A} (f h : A -> bool) l, (forall x, f x = h x) -> forallb_lazy f l = forallb_lazy h l.
Proof. intros A f h l H. induction l as [|x t IH]; cbn; [reflexivity|]. rewrite H, IH. reflexivity. Qed.

Definition leaf_matchesA' (g : positive) (L : axst) (targets : list axst) : bool := ltac2:(tb__ "0|0|
S37SaS30Vg;VL;A2Vtargets;A3").
Lemma leaf_matchesA'_eq : ltac2:(tb__ "0|0|
S15SaS1SaA1S14S0S31R3R2R1A3S1dR3R2R1A3A3Ftargets;FL;Fg;").
Proof. intros. unfold leaf_matchesA', leaf_matchesA. apply existsb_lazy_ext. intros x. apply leaf_matches1A'_eq. Qed.

Definition leaf_okA' (g : positive) (targets : list axst) (L : leafA) : bool := ltac2:(tb__ "0|1|
S0S0L_;S20SfVL;A1M0A1S7S31Vg;G0Vtargets;A3X0x2").
Lemma leaf_okA'_eq_ref : ltac2:(tb__ "0|0|
S15S1SaA1SbS14S0S2dR3R2R1A3S1fR3R2R1A3A3FL;Ftargets;Fg;").
Proof. intros. unfold leaf_okA', leaf_okA_ref. rewrite leaf_matchesA'_eq. reflexivity. Qed.

Lemma leaf_okA'_eq : ltac2:(tb__ "0|0|
S15S1SaA1SbS14S0S2dR3R2R1A3S1eR3R2R1A3A3FL;Ftargets;Fg;").
Proof.
  intros g targets L. rewrite leaf_okA_ref_eq. apply leaf_okA'_eq_ref.
Qed.

Definition check_cutA' (fuel : nat) (cutpcs : list Z) (g : positive) (targets : list axst) (T : axst) : bool := ltac2:(tb__ "0|2|
S0S0L_;S5S5S42Vg;S2aScVT;A1M0A1A2S9S29G0A1A1A2SdVT;A1A2S3S1SbA1M1A1S0Lx;S10Vsegs;Vfuel;Vcutpcs;VT;S7A5G1S36SbS2dVg;Vtargets;A2R1A3Lleaves;S4X3x2S4X0x2").
Lemma check_cutA'_eq : ltac2:(tb__ "0|0|
S2S1S16A1S15S1SaA1SaS14S0S2eR5R4R3R2R1A5S19Vsegs;R5R4R3R2R1A6A3FT;Ftargets;Fg;Fcutpcs;Ffuel;").
Proof.
  intros. unfold check_cutA', check_cutA. destruct (_ && _ && _); [|reflexivity].
  destruct (sym_runA segs fuel cutpcs T true); [|reflexivity]. apply forallb_lazy_ext. intros x. apply leaf_okA'_eq.
Qed.

Definition check_cfgA' (fuel : nat) (cutpcs : list Z) (g : positive) (cuts exits : list axst) : bool := ltac2:(tb__ "0|0|
S36SaS2eVfuel;Vcutpcs;Vg;S8SaVcuts;Vexits;A3A4Vcuts;A3").
Lemma check_cfgA'_eq : ltac2:(tb__ "0|1|
S2S1S16A1S15S1SaA1M0G0S14S0S33R5R4R3R2R1A5S18Vsegs;R5R4R3R2R1A6A3Fexits;Fcuts;Fg;Fcutpcs;Ffuel;").
Proof. intros. unfold check_cfgA', check_cfgA. apply forallb_lazy_ext. intros x. apply check_cutA'_eq. Qed.

Lemma forallb_lazy_cons_true : forall {A} (f : A -> bool) (x : A) (l : list A),
  f x = true -> forallb_lazy f l = true -> forallb_lazy f (x :: l) = true.
Proof. intros A f x l H1 H2. cbn [forallb_lazy]. rewrite H1. exact H2. Qed.

Fixpoint first_matchA' (g : positive) (L : axst) (targets : list axst) (j : nat) : option (nat * wsub) :=
  match targets with
  | [] => None
  | X :: rest =>
      if leaf_matches1A' g L X then Some (j, infer_sub g (ax_S L) (ax_S X))
      else first_matchA' g L rest (S j)
  end.
Lemma first_matchA'_eq : ltac2:(tb__ "0|0|
S15SaS1SaA1S2S14S3S6S2S2bA2A1S34R4R3R2R1A4S1bR4R3R2R1A4A3Fj;Ftargets;FL;Fg;").
Proof.
  intros g L targets. induction targets as [|X rest IH]; intros j; cbn; [reflexivity|].
  rewrite leaf_matches1A'_eq, IH. reflexivity.
Qed.

Fixpoint leaves_edgesA' (g : positive) (i : nat) (leaves : list leafA) (targets : list axst) : option (list edgeA) :=
  match leaves with
  | [] => Some []
  | L :: rest =>
      if leaf_refuted (la_state L) then leaves_edgesA' g i rest targets else
      match first_matchA' g (la_state L) targets 0, leaves_edgesA' g i rest targets with
      | Some (j, s), Some es => Some (mkEdgeA i (la_state L) j s :: es)
      | _, _ => None
      end
  end.
Lemma leaves_edgesA'_eq_ref : ltac2:(tb__ "0|0|
S15S2S1SbA1S1SaA1S14S3S1S17A1A1S32R4R3R2R1A4S22R4R3R2R1A4A3Ftargets;Fleaves;Fi;Fg;").
Proof.
  intros g i leaves targets. induction leaves as [|L rest IH]; cbn; [reflexivity|].
  rewrite first_matchA'_eq, IH. reflexivity.
Qed.

Lemma leaves_edgesA'_eq : ltac2:(tb__ "0|0|
S15S2S1SbA1S1SaA1S14S3S1S17A1A1S32R4R3R2R1A4S21R4R3R2R1A4A3Ftargets;Fleaves;Fi;Fg;").
Proof.
  intros g i leaves targets. rewrite leaves_edgesA_ref_eq. apply leaves_edgesA'_eq_ref.
Qed.

Fixpoint cuts_edgesA' (fuel : nat) (cutpcs : list Z) (g : positive) (i : nat)
         (cuts : list axst) (targets : list axst) : option (list edgeA) :=
  match cuts with
  | [] => Some []
  | T :: rest =>
      if negb (Pos.leb g (ss_next (ax_S T)) && negb (ss_lenient (ax_S T)) && axwf T) then None else
      match sym_runA segs fuel cutpcs T true with
      | Some leaves =>
          match leaves_edgesA' g i leaves targets, cuts_edgesA' fuel cutpcs g (S i) rest targets with
          | Some es, Some es' => Some (es ++ es')
          | _, _ => None
          end
      | None => None
      end
  end.
Lemma cuts_edgesA'_eq : ltac2:(tb__ "0|1|
S2S1S16A1S15S2S1SaA1M0G0S14S3S1S17A1A1S2fR6R5R4R3R2R1A6S1aVsegs;R6R5R4R3R2R1A7A3Ftargets;Fcuts;Fi;Fg;Fcutpcs;Ffuel;").
Proof.
  intros fuel cutpcs g i cuts. revert i. induction cuts as [|T rest IH]; intros i targets; cbn; [reflexivity|].
  destruct (negb _); [reflexivity|]. destruct (sym_runA segs fuel cutpcs T true); [|reflexivity].
  rewrite leaves_edgesA'_eq, IH. reflexivity.
Qed.

Section RC.
Variable g vn ln lp : positive.
Variable X : list (sv * sv).
Variable xb : sv.

Definition check_rcfgA' (fuel : nat) (cutpcs : list Z) (cuts exits : list rnode) : bool := ltac2:(tb__ "0|2|
S5S3cS23S24Vg;Vvn;Vln;Vlp;A4Vcuts;A3S3S1S17A1M0A1S0Lx;S2fVfuel;Vcutpcs;Vg;U0S35S23SaS41VX;Vxb;A2Vcuts;A4S35S23SaS40VX;Vxb;A2S8S23Vcuts;Vexits;A3M1A4A6G0S3cS17S17S25Vg;Vvn;Vln;Vlp;G1S3fR1A1A6Le;R1A3Les;S4X3x2A2").
Lemma check_rcfgA'_eq : ltac2:(tb__ "0|1|
S2S1S16A1S1S23A1M0G0S14S0S3dR4R3R2R1A4S3eVsegs;Vg;Vvn;Vln;Vlp;VX;Vxb;R4R3R2R1AbA3Fexits;Fcuts;Fcutpcs;Ffuel;").
Proof. intros. unfold check_rcfgA', check_rcfgA. rewrite cuts_edgesA'_eq. reflexivity. Qed.
End RC.

End F.
