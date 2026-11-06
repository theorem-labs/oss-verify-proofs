(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "rw"; "eval"; "valuation"; "sobj"; "sprop"; "holds"; "obj_range"; "outside_all"; "ss_facts"; "SLit"; "ss_next"; "swf"; "@Corelib.Init.Logic"; "eq"; "@stdpp.bitvector.definitions"; "bv"; "bv_unsigned"; "@Corelib.Init.Datatypes"; "prod"; "cons"; "nil"; "pair"; "true"; "bool"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.StepA"; "ax_S"; "axst"; "axwf"; "ax_setS"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.LibA.PinA"; "pinA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymFrame"; "obj_subst"; "rho_sub"; "subst_state"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A.SoundA"; "SPA"; "jpredA"; "@Corelib.Lists.ListDef"; "Forall"; "map"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sv_vars_all"; "@Stdlib.Lists.List"; "In"; "@Stdlib.ZArith.BinInt.Z"; "modulo"; "pow"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundA SymSoundM SymFrame SymEntail SymSummary.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3A Require Import Virt StepA SoundA.
Import ListNotations.
Open Scope Z_scope.

Definition pinA (A : axst) (v : positive) (e : sv) : axst := ltac2:(tb__ "0|2|
S1cVA;S20S13S12S0S2A2M0S15S0S2Vv;Ve;A4S14G0A1A3S19VA;A1M1SdG1A1A3A2").

Lemma sv_vars_all_true : ltac2:(tb__ "0|0|
S2SfS17S27S0S16L_;R1A2S16A3Fx;").
Proof. induction x; cbn; rewrite ?IHx1, ?IHx2, ?IHx; reflexivity. Qed.

Section Pin.
Variable segs : list Segment.

Lemma rho_sub_pin_rw : ltac2:(tb__ "0|2|
S5S0S2S0SfS10Q40A1M0S3R4R3A2S4R4R2A2A3SfG0S3R5R2A2S3S1fR5S13S12S0S2A2M1S15S0S2R4R3A4S14G1A1A3A2R2A2A3F_;Fu;Fe;Fv;Frho;").
Proof.
  intros rho v e u Hv. unfold rho_sub. cbn [rw]. unfold wsub_get. cbn [find fst snd].
  destruct (Pos.eqb u v) eqn:E; cbn [eval].
  - apply Pos.eqb_eq in E. subst u. exact Hv.
  - reflexivity.
Qed.

Lemma eval_pin : ltac2:(tb__ "0|2|
S5S0S2S2SfS10Q40A1M0S3R4R3A2S4R4R2A2A3SfG0S4S1fR5S13S12S0S2A2M1S15S0S2R4R3A4S14G1A1A3A2R2A2S4R5R2A2A3F_;Fx;Fe;Fv;Frho;").
Proof.
  intros rho v e x Hv. symmetry. apply (eval_agree_vars (fun _ => true)).
  - intros u _. exact (rho_sub_pin_rw rho v e u Hv).
  - intros l. reflexivity.
  - apply sv_vars_all_true.
Qed.

Lemma obj_range_pin : ltac2:(tb__ "0|1|
S5S0S2S6SfS10Q40A1S3R4R3A2S4R4R2A2A3SfS12S1S1A2S9R5S1eS13S12S0S2A2M0S15S0S2R4R3A4S14G0A1A3R2A2A2S9R5R2A2A3F_;Fo;Fe;Fv;Frho;").
Proof.
  intros rho v e o Hv. rewrite obj_range_subst. unfold obj_range, obj_lo_of, obj_hi_of, soff.
  rewrite !(eval_pin rho v e _ Hv). reflexivity.
Qed.

Lemma outside_all_pin : ltac2:(tb__ "0|2|
S5S0S2S18S6A1S10Q40A1M0SfG0S3R5R4A2S4R5R3A2A3SaR6R3R2A3SaR7S24S6S6S1eS13S12S0S2A2M1S15S0S2R6R5A4S14G1A1A3A1R4A4R3A3F_;F_;Fa;Fobjs;Fe;Fv;Frho;").
Proof.
  intros rho v e objs a Hv H. unfold outside_all in *. rewrite Forall_forall in H |- *. intros o' Ho'.
  apply in_map_iff in Ho' as (o & <- & Ho). cbv zeta. rewrite (obj_range_pin rho v e o Hv). exact (H o Ho).
Qed.

Lemma axwf_pinA : ltac2:(tb__ "0|0|
S1aS0S2SfS17S1bS1dR3R2R1A3A1S1bR3A1A3Fe;Fv;FA;").
Proof. intros A v e. reflexivity. Qed.

Lemma SPA_pin : ltac2:(tb__ "0|1|
S22S5S18S10Q40A1M0A1S1aS0S2S25SfS17SeS19S1dR4R3R2A3A1A1S16A3SfS17S26S0S16L_;S19R5A1A2S16A3SfG0S3R8R5A2S4R8R4A2A3S21Vsegs;RaR7R9R8R4A6S21Vsegs;RbS1dR8R7R6A3RaR9R5A6F_;F_;F_;F_;Fw;Fe;Fv;FA;Ftp;Frho;FJ;").
Proof using .
  intros J rho tp A v e w Hwf Hall Hv [(Hsm & HMI & Hax & Hsh & Hz) HJ]. split; [|exact HJ].
  split; [|split; [exact HMI | split; [rewrite axwf_pinA; exact Hax | split; [|exact Hz]]]].
  - cbn [ax_S pinA ax_setS]. apply smatch_subst_intro; [exact Hwf|].
    apply (smatch_agree_vars segs (fun _ => true) rho (rho_sub rho [(v, e)]) (ax_S A) (virt tp w));
      [ | reflexivity | reflexivity | exact Hall | exact Hsm].
    intros u _. exact (rho_sub_pin_rw rho v e u Hv).
  - unfold pinA. apply shadow_ok_transport_objs; [|exact Hsh].
    intros x _ Ho _. cbn [ss_objs subst_state]. apply outside_all_pin; [exact Hv | exact Ho].
Qed.

Lemma pin_of_fact : ltac2:(tb__ "0|1|
S5S1aS0S2S7S23S7S8R5A1SbS19R4A1A1A3S28S7R2SbS19R5A1A1A3S8R7R3A2SfS10Q40A1S3R8R6A2S4R8R5A2A3M0F_;G0F_;F_;F_;Fp;Fe;Fv;FA;Frho;").
Proof. intros rho A v e p HF Hin Himp. apply Himp. exact (proj1 (Forall_forall _ _) HF p Hin). Qed.

Lemma pin_lit_of_unsigned : ltac2:(tb__ "0|1|
S5S0S1SfS1S11Q40M0S3R3R2A2A2S29R1S2aZ2Z40A2A2A3SfS10G0A1S3R4R3A2S4R4ScR2A1A2A3F_;Fz;Fv;Frho;").
Proof.
  intros rho v z H. cbn [eval]. apply bv_eq. rewrite H, Z_to_bv_unsigned. reflexivity.
Qed.
End Pin.
