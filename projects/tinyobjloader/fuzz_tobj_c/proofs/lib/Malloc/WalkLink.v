(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "positive"; "@Corelib.Init.Logic"; "eq"; "and"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "valuation"; "sv"; "rl"; "rm"; "rw"; "eval"; "sprop"; "sstate"; "agree_below"; "holds"; "swf"; "@Corelib.Init.Datatypes"; "list"; "prod"; "bool"; "true"; "fst"; "option"; "negb"; "Some"; "false"; "pair"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.WalkLink.WithSegs"; "set_vars"; "agrees"; "below200"; "in_vars"; "@stdpp.bitvector.definitions"; "bv"; "@Corelib.Lists.ListDef"; "map"; "Forall"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SP"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.Glue3"; "diffs_ok"; "state_diff"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSummary"; "state_vars_all"; "sv_vars_all"; "@Stdlib.Lists.List"; "forallb"; "@Stdlib.PArith.BinPos.Pos"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundI SymSoundM SymSoundR SymFrame SymSummary SymCall SymEntail Glue3 ExampleMemcpy.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section WithSegs.
Variable segs : list Segment.

Fixpoint set_vars (rho : valuation) (l : list (positive * sv)) : valuation :=
  match l with
  | [] => rho
  | (v, e) :: t => set_vars (rho_set_rw rho v (eval rho e)) t
  end.

Definition in_vars (l : list positive) (v : positive) : bool := existsb (Pos.eqb v) l.

Lemma set_vars_rl : ltac2:(tb__ "0|0|
S3SeSfS0S4A2A1S1S0SeS1cQ8A1A1F_;S5S18R2R1A2A1S5R2A1A3Fl;Frho;").
Proof using . intros rho l. revert rho. induction l as [|[v e] t IH]; intros rho; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma set_vars_rm : ltac2:(tb__ "0|0|
S3SeSfS0S4A2A1S1S1cQ40A1S13S1cQ8A1A1F_;S6S18R2R1A2A1S6R2A1A3Fl;Frho;").
Proof using . intros rho l. revert rho. induction l as [|[v e] t IH]; intros rho; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.
Lemma set_vars_other : ltac2:(tb__ "0|1|
S3SeSfS0S4A2M0A1S0S1S10S1bS1dG0S0S12S0S4A2R2A4R1A2S16A3S1S1cQ40A1S7S18R4R3A2R2A2S7R4R2A2A3F_;Fv;Fl;Frho;").
Proof using .
  intros rho l. revert rho. induction l as [|[u e] t IH]; intros rho v Hv; [reflexivity|].
  cbn in Hv. apply Bool.orb_false_iff in Hv as [H1 H2]. cbn. rewrite IH by exact H2. cbn [rw rho_set_rw]. rewrite H1. reflexivity.
Qed.

Lemma relink : ltac2:(tb__ "0|4|
SeS21A1S20OF_;F_;S3SaSaS22SeSfS0S4A2M0A1SeSfS4S4A2A1M1SeS9A1M2S1S10S25S0S14S1bS1dG0S0S12S0S4A2R4A4R1A2A1Lv;R6A2S11A3S1S10SdR6A1S11A3S1S13SfG1G2A2M3A1S24R8R7A2S15G3S17G1G2R4R3A4A2A3S23S18RaR6A2R5A2S1eS9ScS18RbR7A2A1R5A3S1fVsegs;RdRbRcR9A5S1fVsegs;ReRbS18RdR9A2RaA5F_;F_;F_;F_;F_;F_;Fnf;Fd;Fl;Fw;FS';FS;Frho;FK;").
Proof using .
  intros K rho S S' w l d nf Hvars Hwf Hsd Hd Hnf HSP.
  eapply SP_restate; [exact Hwf | exact Hsd | exact Hd | exact Hnf |].
  destruct HSP as [Hsm HK]. split; [|exact HK].
  apply (smatch_agree_vars segs (fun v => negb (in_vars (map fst l) v)) rho); try assumption.
  - intros v Hv. symmetry. apply set_vars_other. destruct (in_vars (map fst l) v); [discriminate|reflexivity].
  - intros l0. rewrite set_vars_rl. reflexivity.
  - rewrite set_vars_rm. reflexivity.
Qed.

Definition below200 (v : positive) : bool := (v <? 200)%positive.

Definition agrees (rho1 rho : valuation) : Prop := ltac2:(tb__ "0|2|
S2S0S1S10S1aR1A1S11A3S1S1cQ40A1M0S7Vrho;R2A2S7Vrho1;R2A2A3F_;Fv;S2S0S1SeS1cQ8A1M1A1S5Vrho;R1A2S5Vrho1;R1A2A3Fl;S1G0S13G1A1F_;S6Vrho;A1S6Vrho1;A1A3A2A2").

Lemma agrees_refl : ltac2:(tb__ "0|0|
S3S19R1R1A2Frho;").
Proof using . intros rho. repeat split; intros; reflexivity. Qed.

Lemma agrees_set_vars : ltac2:(tb__ "0|1|
S3S3SeSfS0S4A2M0A1S19R3R2A2S1S10S27S0S0S14S1aR1A1A1Lv;S1dG0S0S12S0S4A2R2A4A3S11A3S19R5S18R4R3A2A2F_;F_;Fl;Frho;Frho1;").
Proof using .
  intros rho1 rho l (Hw & Hl & Hm) Hb. split; [|split; [intros l0; rewrite set_vars_rl; apply Hl | rewrite set_vars_rm; exact Hm]].
  intros v Hv. rewrite set_vars_other; [apply Hw; exact Hv|].
  rewrite forallb_forall in Hb. destruct (in_vars (map fst l) v) eqn:E; [|reflexivity].
  unfold in_vars in E. apply existsb_exists in E as (u & Hu & E). apply Pos.eqb_eq in E. subst u.
  specialize (Hb v Hu). rewrite Hv in Hb. discriminate.
Qed.

Lemma agrees_below : ltac2:(tb__ "0|0|
S3S3S3S0S19R4R3A2SbR2R4R3A3S28Pc8R3A2S19R7R5A2F_;F_;F_;Fn;Frho';Frho;Frho1;").
Proof using .
  intros rho1 rho rho' n (Hw & Hl & Hm) (Aw & Al & Am) Hn.
  split; [|split].
  - intros v Hv. rewrite <- (Aw v) by (unfold below200 in Hv; apply Pos.ltb_lt in Hv; lia). apply Hw. exact Hv.
  - intros l. rewrite <- (Al l). apply Hl.
  - apply FunctionalExtensionality.functional_extensionality. intros a. rewrite <- (Am a). rewrite Hm. reflexivity.
Qed.

Lemma eval_agrees : ltac2:(tb__ "0|0|
S3S3S4S19R3R2A2S1S10S26S1aR2A2S11A3S1S1cQ40A1S8R4R3A2S8R5R3A2A3F_;F_;Fe;Frho;Frho1;").
Proof using . intros rho1 rho e (Hw & Hl & _) He. apply (eval_agree_vars below200); auto. Qed.

End WithSegs.
