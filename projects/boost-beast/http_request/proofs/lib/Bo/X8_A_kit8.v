(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX Bytes Exec.
From OSSVerify.Proofs.boost_beast.http_request.lib.Spec Require Import Prelim.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import BSegs AsShadow AsConst AsImgSh AsIface AsCXXHeap AsWalk AsStack0 AXPres AXKit AXRep AXRep2 AsTRList.
From OSSVerify.Proofs.boost_beast.http_request.lib.Bo Require Import N8Kit N8Kit2 N8Kit3 X8Kit X8SRKit X8_A_kit X8_A_kit2 X8_A_kit3 X8_A_kit4.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps H.

  Lemma fresh_frame_tail : forall f LF k ff fp, fresh_frame H (f :: LF) k ff fp -> fresh_frame H LF k ff fp.
  Proof.
    intros f LF k ff fp (AR & FB & D). split; [exact AR|]. split; [exact FB|]. intros g Hg. apply D. right. exact Hg.
  Qed.

  Lemma fs_scratch_tail : forall f LF iv, fs_scratch H (f :: LF) iv -> fs_scratch H LF iv.
  Proof.
    intros f LF iv [E|(k & ff & fp & FF & E)]; [left; exact E| right].
    exists k, ff, fp. split; [eapply fresh_frame_tail; exact FF| exact E].
  Qed.

  Lemma Forall_scratch_tail : forall f LF XS, Forall (fs_scratch H (f :: LF)) XS -> Forall (fs_scratch H LF) XS.
  Proof. intros f LF XS FX. eapply Forall_impl; [| exact FX]. intros iv K. eapply fs_scratch_tail. exact K. Qed.

  (* [comment removed for export] *)
  Lemma live_frame_off_scratch : forall LF k ff fp m XS a n,
    as_RFS H ((k, ff, fp) :: LF) m -> Forall (fs_scratch H ((k, ff, fp) :: LF)) XS ->
    ff <= a -> a + n <= ff + fsz k -> 0 <= n ->
    Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) XS.
  Proof.
    intros LF k ff fp m XS a n RF FX H1 H2 Hn.
    pose proof (ff_facts H _ _ _ _ (fresh_of_RFS H HH _ _ _ _ _ RF)) as (K0 & FP & NP & E8 & F1 & F2 & F3 & F3' & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & APF & _).
    pose proof aceil_facts as (AF & _).
    eapply (Forall_scratch H HH); [exact RF| | exact Hn| unfold AAPP_HI; lia| eapply aapp_sub; [exact APF| lia| lia]| exact FX].
    eapply (fsobj_inframe H); [left; reflexivity| cbn; lia| cbn; lia].
  Qed.

  Lemma live_shadow_off_scratch : forall LF k ff fp m XS,
    as_RFS H ((k, ff, fp) :: LF) m -> Forall (fs_scratch H ((k, ff, fp) :: LF)) XS ->
    Forall (fun iv : Z * Z => sh ff + fshn k <= fst iv \/ snd iv <= sh ff) XS.
  Proof.
    intros LF k ff fp m XS RF FX.
    pose proof (ff_facts H _ _ _ _ (fresh_of_RFS H HH _ _ _ _ _ RF)) as (K0 & FP & NP & E8 & F1 & F2 & F3 & F3' & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12 & APF & _).
    pose proof aceil_facts as (AF & _).
    rewrite (fshn_nsh k) by lia.
    eapply (Forall_scratch_sh H HH); [exact RF| | lia| unfold AAPP_HI; lia| exact APF| exact FX].
    eapply (fsobj_inframe H); [left; reflexivity| cbn; lia| cbn; lia].
  Qed.

  Lemma live_flag_off_scratch : forall LF k ff fp m XS,
    as_RFS H ((k, ff, fp) :: LF) m -> Forall (fs_scratch H ((k, ff, fp) :: LF)) XS ->
    Forall (fun iv : Z * Z => fp + 1 <= fst iv \/ snd iv <= fp) XS.
  Proof.
    intros LF k ff fp m XS RF FX. eapply Forall_impl; [| exact FX]. intros iv K. eapply (scratch_flag H HH); [exact RF| exact K].
  Qed.

End HCW.
