(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsImgSh AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8SRKit XA_leaves X8_A_kit X8_A_kit2 X8_A_kit3 X8_A_kit4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.

  (* [comment removed for export] *)
  Lemma AXS_system_cat : forall m, AXStatics2 m ->
    rw_cells asegs m AG_SYSTEM_CAT_INST [C8 (Z_to_bv 64 AW_SYSTEM_CAT_VPTR); C8 (Z_to_bv 64 W_SYSTEM_CAT_ID)].
  Proof.
    intros m XS. destruct XS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & H0 & _).
    unfold wcells, wz in H0. cbn [map] in H0. exact H0.
  Qed.

  (* [comment removed for export] *)
  Lemma ACanaryReads_hi : forall W m m',
    ACanaryReads m -> munch W m m' -> Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> ACanaryReads m'.
  Proof.
    intros W m m' CR MU FW.
    assert (D : forall A n, A + n <= AIMG_TOP -> disjoint_from W A n).
    { intros A n HA. clear CR MU. induction W as [|[l h] W IH]; [exact I|].
      pose proof (Forall_inv FW) as H1. cbn in H1. cbn. split; [lia|]. apply IH. exact (Forall_inv_tail FW). }
    eapply ACanaryReads_transport; [exact CR| exact MU| apply D| apply D]; unfold AG_GOT_STACK_CHK, AG_STACK_CHK_GUARD, AIMG_TOP; lia.
  Qed.

  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  (* [comment removed for export] *)
  Lemma ACanaryReads_xpres : forall LB SP X m m',
    ACanaryReads m -> xpres H LB SP X m m' -> Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) X -> ACanaryReads m'.
  Proof.
    intros LB SP X m m' CR XP FX. destruct (ACanaryReads_cells m CR) as (can & _ & [C1 C2]).
    assert (D : forall A n, A + n <= AIMG_TOP -> Forall (fun iv : Z * Z => A + n <= fst iv \/ snd iv <= A) X).
    { intros A n HA. eapply Forall_impl; [| exact FX]. intros [l h] K. cbn [fst snd] in *. lia. }
    apply (ACanaryCells_reads m' can). split.
    - eapply (ro_cells_xpres H); [exact XP| exact C1|]. cbn [cells_size csize Nat.add].
      split; [right; left; intros a Ha; unfold aimg_client, AG_GOT_STACK_CHK in *; lia| apply D; unfold AG_GOT_STACK_CHK, AIMG_TOP; lia].
    - eapply (ro_cells_xpres H); [exact XP| exact C2|]. cbn [cells_size csize Nat.add].
      split; [right; left; intros a Ha; unfold aimg_client, AG_STACK_CHK_GUARD in *; lia| apply D; unfold AG_STACK_CHK_GUARD, AIMG_TOP; lia].
  Qed.

  Lemma ACanaryReads_xpres_scratch : forall LB LF m1 SP XS m m',
    as_RFS H LF m1 -> Forall (fs_scratch H LF) XS -> ACanaryReads m -> xpres H LB SP XS m m' -> ACanaryReads m'.
  Proof.
    intros LB LF m1 SP XS m m' RF FX CR XP. eapply ACanaryReads_xpres; [exact CR| exact XP|].
    eapply Forall_impl; [| exact FX]. intros iv FS. pose proof (scratch_facts H HH LF m1 [] iv RF FS) as (_ & K & _). exact K.
  Qed.

End HCW.
