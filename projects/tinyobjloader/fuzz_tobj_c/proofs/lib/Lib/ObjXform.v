(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sstate"; "valuation"; "smatch"; "sobj"; "ss_objs"; "sv"; "@Corelib.Init.Datatypes"; "list"; "nat"; "Some"; "option"; "bool"; "andb"; "prod"; "None"; "length"; "true"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.ObjXform"; "xform"; "apply_xforms"; "apply_xform"; "select_ok"; "@Corelib.Init.Logic"; "eq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "SPJ"; "jpred"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "event"; "Model"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "etriple"; "triple"; "assn"; "@LinuxProcessSemantics.LinuxProcessSem.Run"; "config"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymEntail"; "memN"; "nodupN"; "select"; "@Stdlib.Lists.List"; "forallb"; "In"; "@Corelib.Lists.ListDef"; "seq"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymObj"; "merge_objs_at"; "rebase_obj_at"; "split_obj_at"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymStep"; "set_objs"; "@Stdlib.Arith.PeanoNat.Nat"; "ltb"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Lia Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundI SymSoundL SymSoundM SymSoundR SymObj SymEntail SymCFG Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Inductive xform :=
| XSplit (i : nat) (mid : sv)
| XMerge (i : nat)
| XRebase (i : nat)
| XSelect (idxs : list nat).

Definition select_ok (n : nat) (idxs : list nat) : bool := ltac2:(tb__ "0|0|
SbSbS20Vidxs;A1S22S7S7S29R1Vn;A2Li;Vidxs;A3A2S22S7S7S1fR1Vidxs;A2Li;S24U0Vn;A2A3A2").

Definition apply_xform (S : sstate) (x : xform) : option sstate := ltac2:(tb__ "0|2|
S10S9S0A1M0Lx;Vx;S7S5S27VS;R2R1A3Lmid;Li;S7S25VS;R1A2Li;S7S26VS;R1A2Li;S6S7A1SaG0L_;S13SeS3S4VS;A1M1A2R1A2S8S0S28VS;S21G1R1A2A2A2SdS0A1Xax2Lidxs;X10x4").

Fixpoint apply_xforms (S : sstate) (xs : list xform) : option sstate :=
  match xs with
  | [] => Some S
  | x :: r => match apply_xform S x with Some S' => apply_xforms S' r | None => None end
  end.

Section X.
Variable segs : list Segment.

Lemma memN_In' : ltac2:(tb__ "0|0|
S7S6S7A1S14SaS1fR2R1A2SfA3S23S7R3R2A3F_;Fl;Fi;").
Proof using .
  induction l as [|x t IH]; cbn; intros H; [discriminate|].
  apply Bool.orb_true_iff in H as [H|H]; [left; apply Nat.eqb_eq in H; lia | right; auto].
Qed.

Lemma smatch_xform : ltac2:(tb__ "0|0|
S1S0S10S0ScS6S18A1S1eA2S14S9S0A1S12R4R3A2S8S0R2A2A3S2Vsegs;R6R5R2A4S2Vsegs;R7R4R3A4F_;F_;Fw;FS';Fx;FS;Frho;").
Proof using .
  intros rho S x S' w Hx Hsm. destruct x as [i mid|i|i|idxs]; cbn [apply_xform] in Hx.
  - eapply smatch_split; eauto.
  - eapply smatch_merge; eauto.
  - eapply smatch_rebase; eauto.
  - destruct (select_ok (length (ss_objs S)) idxs) eqn:E; [|discriminate]. injection Hx as <-.
    unfold select_ok in E. apply andb_prop in E as [E Hcov]. apply andb_prop in E as [Hnd Hlt].
    apply smatch_select; [exact Hsm | exact Hnd | |].
    + intros i Hi. apply (proj1 (forallb_forall _ _) Hlt) in Hi. apply Nat.ltb_lt in Hi. exact Hi.
    + intros i Hi. apply memN_In'. apply (proj1 (forallb_forall _ _) Hcov). apply in_seq. lia.
Qed.

Theorem smatch_xforms : ltac2:(tb__ "0|0|
S6S10A1S1S0S0ScS6S18A1S1eA2S14S9S0A1S11R3R5A2S8S0R2A2A3S2Vsegs;R5R4R2A4S2Vsegs;R6R4R3A4F_;F_;Fw;FS';FS;Frho;Fxs;").
Proof using .
  induction xs as [|x r IH]; intros rho S S' w H Hsm; cbn [apply_xforms] in H.
  - injection H as <-. exact Hsm.
  - destruct (apply_xform S x) as [S1|] eqn:E; [|discriminate].
    eapply IH; [exact H|]. eapply smatch_xform; eauto.
Qed.

Lemma SP_xforms : ltac2:(tb__ "0|0|
S6S18A1S19OF_;F_;S6S10A1S1S0S0S1aS14S9S0A1S11R3R5A2S8S0R2A2A3S15Vsegs;R7R4R5R2A5S15Vsegs;R8R4R6R3A5F_;F_;Fw;FS';FS;Frho;Fxs;FK;").
Proof using . intros K xs rho S S' w H [Hsm Hk]. split; [eapply smatch_xforms; eauto | exact Hk]. Qed.

Lemma SPJ_xforms : ltac2:(tb__ "0|0|
S17S6S10A1S1S0S0S1aS14S9S0A1S11R3R5A2S8S0R2A2A3S16Vsegs;R7R4R5R2A5S16Vsegs;R8R4R6R3A5F_;F_;Fw;FS';FS;Frho;Fxs;FJ;").
Proof using . intros J xs rho S S' w H [Hsm Hk]. split; [eapply smatch_xforms; eauto | exact Hk]. Qed.

Lemma triple_xforms : ltac2:(tb__ "0|0|
S1aOF_;S6S18A1S19OF_;F_;S6S10A1S1S0S0S1dS14S9S0A1S11R3R5A2S8S0R2A2A3S1cVsegs;R8S15Vsegs;R7R3R5A4R2A4S1cVsegs;R9S15Vsegs;R8R5R6A4R3A4F_;F_;FQ;FS';FS;Frho;Fxs;FK;Fok;").
Proof using .
  intros ok K xs rho S S' Q H HT. eapply triple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. eapply SP_xforms; eauto.
Qed.

Lemma etriple_xforms : ltac2:(tb__ "0|0|
S6S18A1S19OF_;F_;S6S10A1S1S0S0S1aOF_;S14S9S0A1S11R3R5A2S8S0R2A2A3S1bVsegs;S15Vsegs;R7R3R5A4R2A3S1bVsegs;S15Vsegs;R8R5R6A4R3A3F_;F_;FQ;FS';FS;Frho;Fxs;FK;").
Proof using .
  intros K xs rho S S' Q H HT. eapply etriple_conseq; [| intros w Hw; exact Hw | exact HT].
  intros w Hw. eapply SP_xforms; eauto.
Qed.
End X.
