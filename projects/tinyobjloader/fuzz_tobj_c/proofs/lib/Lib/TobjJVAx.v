(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "sv"; "valuation"; "sstate"; "@Corelib.Init.Datatypes"; "list"; "prod"; "app"; "cons"; "nil"; "Some"; "option"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVA"; "JGA"; "amode"; "XA"; "nodes_ok"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymSoundR"; "SPJ"; "jpred"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw.Safety"; "world"; "@Stdlib.Sorting.Permutation"; "Permutation"; "@LinuxProcessSemantics.LinuxProcessSem.State"; "Model"; "event"; "@Corelib.Numbers.BinNums"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocIface"; "MA"; "@Corelib.Init.Logic"; "eq"; "@LinuxProcessSemantics.LinuxProcessSem.MemImageType"; "Segment"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJV"; "JG"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TobjJVAx"; "nstep"; "run_nsteps"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia Permutation.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import MallocModel MallocInv MallocLayout MallocIface MallocLaws.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import
  SymState SymStep SymSoundA SymSoundB SymSoundV SymSoundL SymSoundI SymSoundM SymSoundR SymFrame SymEntail SymCFG SymSummary SymObj ExampleMemcpy Glue3.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import Contract.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import CursorGlue ObjUnbase ObjXform TobjJV TobjJVx TobjArena TobjJVA.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Section X.
Variable segs : list Segment.
Variable C : mconsts.
Variable NP : positive.
Variable Kc : ltac2:(tb__ "0|0|
S3S13A1S12OF_;F_;").
Variable rho0 : valuation.
Variable P0f : valuation -> Prop.
Variable FB : list (Z * Z).

Lemma JGA_JG : ltac2:(tb__ "0|0|
S3S4S0S0A2A1SbS1S3S13A1S12SaVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R5R4R3R2R1AcS18Vsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R6R4R3R2AbF_;Fmd;Ftr;Frho;Fam;Ftv;").
Proof using . intros tv am rho tr md [Ai [HJ _]]. exists Ai. exact HJ. Qed.

Lemma nodes_ok_perm : ltac2:(tb__ "0|2|
S15S1S3S4S0S0A2M0A1M1G1S3S4S14S14A2A1S11G0R3R2A3SdVFB;R6R5R4R2A5SdVFB;R7R6R4R3A5F_;F_;Fns;Ftv';Ftv;Frho;FAi;").
Proof using .
  intros Ai rho tv tv' ns HP [HF HD]. split; [|exact HD].
  apply Forall_forall. intros bc Hbc. destruct (proj1 (Forall_forall _ _) HF bc Hbc) as (A & B & Ct).
  split; [exact A|]. split; [exact B|]. intros t Ht. apply Ct. eapply Permutation_in; [apply Permutation_sym; exact HP | exact Ht].
Qed.

Lemma XA_perm : ltac2:(tb__ "0|2|
SbS15S1S3S4S0S0A2M0A1M1G1S11G0R2R1A3ScVFB;R6R5R4R3A5ScVFB;R7R6R5R3A5F_;F_;Ftv';Ftv;Frho;FAi;Fam;").
Proof using .
  intros am Ai rho tv tv' HP HX. destruct am as [|hd|hd nx cap sl|hd g]; cbn -[HDR] in HX |- *.
  - exact I.
  - destruct HX as (ns & HA & HN). exists ns. split; [exact HA | exact (nodes_ok_perm _ _ _ _ _ HP HN)].
  - destruct HX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & ns & HA & HN & Hnin).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split.
    + intros t Ht. apply X5. eapply Permutation_in; [apply Permutation_sym; exact HP | exact Ht].
    + split; [exact X6|]. split; [exact X7|]. exists ns. split; [exact HA|]. split; [exact (nodes_ok_perm _ _ _ _ _ HP HN) | exact Hnin].
  - destruct HX as (ns & HA & HN & HL). exists ns. split; [exact HA|]. split; [exact (nodes_ok_perm _ _ _ _ _ HP HN) | exact HL].
Qed.

Lemma JGA_tv_perm : ltac2:(tb__ "0|2|
S3S4S0S0A2M0A1M1G1SbS1S3S13A1S12S11G0R6R5A3SaVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7R5R4R3R2AcSaVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7R6R5R4R3AcF_;F_;Fmd;Ftr;Frho;Fam;Ftv';Ftv;").
Proof using .
  intros tv tv' am rho tr md HP [Ai [HJ HX]]. exists Ai. split.
  - destruct HJ as (Hav & Hk & HM & HPb & (HN & HD & HZ) & HK & HP0).
    split; [exact Hav|]. split; [exact Hk|]. split; [exact HM|]. split; [exact HPb|]. split; [|split; [exact HK | exact HP0]].
    split; [|split].
    + unfold tvin in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HN).
      eapply Permutation_in; [apply Permutation_sym; exact HP | exact Ht].
    + exact (tvd_perm rho tv tv' HP HD).
    + unfold tvz in *. apply Forall_forall. intros t Ht. apply (proj1 (Forall_forall _ _) HZ).
      eapply Permutation_in; [apply Permutation_sym; exact HP | exact Ht].
  - exact (XA_perm _ _ _ _ _ HP HX).
Qed.

Lemma SPJ_JGA_perm : ltac2:(tb__ "0|2|
S3S4S0S0A2M0A1M1G1SbS2S1S10S11G0R6R5A3SeVsegs;SaVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7R5A9R4R3R2A5SeVsegs;SaVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;R7R6A9R5R4R3A5F_;F_;Fw;Frho;FS;Fam;Ftv';Ftv;").
Proof using . intros tv tv' am S rho w HP [Hs HJ]. split; [exact Hs | exact (JGA_tv_perm _ _ _ _ _ _ HP HJ)]. Qed.

Lemma SPJ_JGA_move_last : ltac2:(tb__ "0|2|
S3S4S0S0A2M0A1M1G1G0SbS2S1S10SeVsegs;SaVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S5G0R7S6G0R5R6A3A3R4A9R3R2R1A5SeVsegs;SaVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S5G0S5G0R8R7A3S6G0R6S7G0A1A3A3R5A9R4R3R2A5F_;Fw;Frho;FS;Fam;Fx;Fl2;Fl1;").
Proof using . intros. eapply SPJ_JGA_perm; [apply perm_move_last | exact H]. Qed.
Lemma SPJ_JGA_move_back : ltac2:(tb__ "0|2|
S3S4S0S0A2M0A1M1G1G0SbS2S1S10SeVsegs;SaVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S5G0S5G0R7R6A3S6G0R5S7G0A1A3A3R4A9R3R2R1A5SeVsegs;SaVsegs;VC;VNP;VKc;Vrho0;VP0f;VFB;S5G0R8S6G0R6R7A3A3R5A9R4R3R2A5F_;Fw;Frho;FS;Fam;Fx;Fl2;Fl1;").
Proof using . intros. eapply SPJ_JGA_perm; [apply Permutation_sym; apply perm_move_last | exact H]. Qed.
End X.

Inductive nstep := NX (xs : list xform) | NU (i : nat) (c : Z).
Fixpoint run_nsteps (S : sstate) (l : list nstep) : option sstate :=
  match l with
  | [] => Some S
  | NX xs :: r => match apply_xforms S xs with Some S' => run_nsteps S' r | None => None end
  | NU i c :: r => match unbase_obj_at S i c with Some S' => run_nsteps S' r | None => None end
  end.
Lemma SPJ_nsteps : ltac2:(tb__ "0|0|
S3S17A1SfS3S19A1S1S2S2S10S16S9S2A1S1aR3R5A2S8S2R2A2A3SeR8R7R4R5R2A5SeR9R8R4R6R3A5F_;F_;Fw;FS';FS;Frho;Fl;FJ;Fsegs;").
Proof.
  intros segs J l. induction l as [|[xs|i c] r IH]; intros rho S S' w H Hw; cbn in H.
  - injection H as <-. exact Hw.
  - destruct (apply_xforms S xs) as [S1|] eqn:E; [|discriminate]. eapply IH; [exact H|]. eapply SPJ_xforms; [exact E | exact Hw].
  - destruct (unbase_obj_at S i c) as [S1|] eqn:E; [|discriminate]. eapply IH; [exact H|]. eapply SPJ_unbase; [exact E | exact Hw].
Qed.
