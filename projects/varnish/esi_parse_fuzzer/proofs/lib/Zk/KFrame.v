(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect Mremap.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import AgentLib RelSpec MmapSim ShapeAlg AllocSim RefNodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Nodes.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.ITree OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Nodes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require Import KNodes RzImpl AllocSpec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import BWorld.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Local Open Scope Z_scope.

(* [comment removed for export] *)
Definition same_env (md md' : Model) : Prop :=
  m_fd md' = m_fd md /\ m_io md' = m_io md /\ m_fsys md' = m_fsys md /\ m_proc md' = m_proc md
  /\ m_lim md' = m_lim md /\ m_time md' = m_time md
  /\ vm_limit (m_vmmaps md') = vm_limit (m_vmmaps md)
  /\ vm_reserved (m_vmmaps md') = vm_reserved (m_vmmaps md)
  /\ vm_mmap_base (m_vmmaps md') = vm_mmap_base (m_vmmaps md)
  /\ vm_init_sp (m_vmmaps md') = vm_init_sp (m_vmmaps md).
(* [comment removed for export] *)

Lemma same_env_refl md : same_env md md.
Proof. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

Lemma same_env_trans a b c : same_env a b -> same_env b c -> same_env a c.
Proof.
  ((first [ intro dR_2; dand10 dR_2 as A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 | intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) ]); (first [ intro dR_3; dand10 dR_3 as B1 B2 B3 B4 B5 B6 B7 B8 B9 B10 | intros (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & B9 & B10) ])).
  OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; congruence.
Qed.

Lemma md_frame_of_same_env md md' : same_env md md' -> KI md' -> md_frame md md'.
Proof.
  ((first [ intro dR_4; dand10 dR_4 as A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 | intros (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10) ]); intros [H L]). unfold md_frame. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; assumption.
Qed.

Lemma same_env_with_vmmaps h md :
  vm_limit h = vm_limit (m_vmmaps md) -> vm_reserved h = vm_reserved (m_vmmaps md) ->
  vm_mmap_base h = vm_mmap_base (m_vmmaps md) -> vm_init_sp h = vm_init_sp (m_vmmaps md) ->   (* [comment removed for export] *)
  same_env md (with_vmmaps h md).
Proof. intros. unfold same_env, with_vmmaps, m_vmmaps in *. destruct md; cbn in *. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; auto. Qed.

Lemma same_env_with_vm_backing l p md : same_env md (with_vm_backing l p md).
Proof. unfold same_env, with_vm_backing, m_vmmaps. destruct md; cbn. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; reflexivity. Qed.

Lemma same_env_vm_forget_range lo hi md : same_env md (vm_forget_range lo hi md).
Proof. unfold vm_forget_range. apply same_env_with_vm_backing. Qed.

Lemma same_env_forget_vm_ranges l : forall md, same_env md (forget_vm_ranges l md).
Proof.
  induction l as [|[a n] l IH]; intros md; cbn; [apply same_env_refl|].
  eapply same_env_trans; [apply same_env_vm_forget_range| apply IH].
Qed.

Lemma same_env_vm_resize_backing b o on d nn md : same_env md (vm_resize_backing b o on d nn md).
Proof. unfold vm_resize_backing. apply same_env_with_vm_backing. Qed.

Lemma nstep_same_env : forall n md eff md', nstep n md eff md' -> same_env md md'.
Proof.
  intros n md eff md' HS. destruct n; cbn -[brk_model mmap_model noaccess_model fixed_noaccess_model
    fixed_destroyed_model munmap_model mprotect_model mremap_model_next Z.eqb] in HS; try contradiction.
  - (first [ dex1 HS as r; dand3 HS as Hr -> -> | dand4 HS as r Hr -> -> | destruct HS as (r & Hr & -> & ->) ]). unfold brk_model, with_brk_next.
    eapply same_env_trans; [| apply same_env_forget_vm_ranges]. apply same_env_with_vmmaps; reflexivity.
  - destruct (flags =? NMAP_ANON)%Z; [destruct (prot =? NPROT_RW)%Z|].
    + destruct HS as [(e & _ & _ & ->)|(a & _ & _ & ->)]; [apply same_env_refl|]. unfold mmap_model. apply same_env_with_vmmaps; reflexivity.
    + destruct HS as [(e & _ & _ & ->)|(a & _ & _ & ->)]; [apply same_env_refl|]. unfold noaccess_model. apply same_env_with_vmmaps; reflexivity.
    + destruct HS as [(e & _ & _ & ->)|[(_ & ->)|(_ & e & _ & _ & ->)]]; [apply same_env_refl| |].
      * unfold fixed_noaccess_model. eapply same_env_trans; [| apply same_env_vm_forget_range]. apply same_env_with_vmmaps; reflexivity.
      * unfold fixed_destroyed_model. eapply same_env_trans; [| apply same_env_vm_forget_range]. apply same_env_with_vmmaps; reflexivity.
  - destruct HS as [-> ->]. unfold munmap_model, with_mmap_destroyed.
    eapply same_env_trans; [| apply same_env_vm_forget_range]. apply same_env_with_vmmaps; reflexivity.
  - destruct HS as [(e & _ & _ & ->)|(_ & _ & ->)]; [apply same_env_refl|]. unfold mprotect_model. apply same_env_with_vmmaps; reflexivity.
  - destruct HS as [(_ & _ & ->)|[_ [(e & _ & _ & ->)|[(_ & _ & ->)|[(_ & _ & _ & ->)|(_ & dst & _ & _ & ->)]]]]];
      try apply same_env_refl; unfold mremap_model_next;
      (eapply same_env_trans; [| apply same_env_vm_resize_backing]); apply same_env_with_vmmaps; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma twf_same_env {BW : BWorld} : forall {R} (t : itree node R) md0 md (P : R -> Model -> Prop),
  same_env md0 md -> twf t md P -> twf t md (fun r md' => P r md' /\ same_env md0 md').
Proof.
  intros R t. induction t as [r|n k IH]; intros md0 md P HE H; cbn in *.
  - split; assumption.
  - destruct H as [Hs Hk]. split; [exact Hs|]. intros eff md' Hst Hgate.
    apply IH; [eapply same_env_trans; [exact HE| eapply nstep_same_env; exact Hst]| apply Hk; [exact Hst| exact Hgate]].
Qed.
