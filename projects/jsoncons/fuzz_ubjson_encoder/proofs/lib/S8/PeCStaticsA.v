(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec StoreOk HeapIface LibIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAEx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PESTA.
Section Statics.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable E : pe_addrs.

Definition ax_list (e : bool) : list (Z * Z) := if e then [(pa_errcat_dtor A, pa_errcat_obj A)] else [].
Lemma ax_list_len e : (length (ax_list e) <= 1)%nat.
Proof. destruct e; cbn; lia. Qed.

Definition atexit_stA (M : word -> option byte) (e : bool) : Prop :=
  HAJ.atexit_cells segs M (pa_atexit A) (paa_atexit_f0 AA) (paa_atexit_a0 AA) (pe_drv_call E) (pe_drv_guard E) (paa_at_cxa_atexit AA) (ax_list e).

Definition err_okA (M : word -> option byte) (e : bool) : Prop :=
  (if e then L5.u8_at segs M (pa_errcat_guard A) 1 else L5.img_clear M (pa_errcat_guard A) (pa_errcat_guard A + 2))
  /\ atexit_stA M e.

Definition ls_okA (g : PMST.st) (M : word -> option byte) : Prop :=
  PMSTA.base_okA segs A M /\ PMST.loc_ok segs A M (PMST.st_loc g) /\ PMST.sys_ok segs A M (PMST.st_sys g) /\ err_okA M (PMST.st_err g).

Definition TopLSA : lib_statics := {| ls_state := PMST.st; LibIface.ls_ok := ls_okA; ls_g0 := PMST.g0 |}.

Lemma atexit_stA_agree (WF : PMST.addrs_wf A) M M' e :
  (forall i, pa_atexit A <= i < pa_atexit A + 544 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> atexit_stA M e -> atexit_stA M' e.
Proof.
  intros AG. pose proof (PMST.aw_atexit A WF) as HX. unfold atexit_stA, HAJ.atexit_cells.
  assert (U8 : forall a v, pa_atexit A <= a -> a + 8 <= pa_atexit A + 544 -> L5.u64_at segs M a v -> L5.u64_at segs M' a v).
  { intros a v H1 H2. apply (L5C.u64_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG. lia. }
  assert (U4 : forall a v, pa_atexit A <= a -> a + 4 <= pa_atexit A + 544 -> L5.u32_at segs M a v -> L5.u32_at segs M' a v).
  { intros a v H1 H2 H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a); [exact H|lia|cbn; lia|]. intros i Hi. apply AG. cbn in Hi. lia. }
  assert (U1 : forall a v, pa_atexit A <= a -> a + 1 <= pa_atexit A + 544 -> L5.u8_at segs M a v -> L5.u8_at segs M' a v).
  { intros a v H1 H2. apply (L5C.u8_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG. lia. }
  pose proof (ax_list_len e) as LEN.
  intros (F & LK & SL & HD & NX & F0 & A0 & F1 & A1 & EXT).
  split; [apply U1; [lia|lia|exact F]|]. split; [apply U4; [lia|lia|exact LK]|]. split; [apply U4; [lia|lia|exact SL]|].
  split; [apply U8; [lia|lia|exact HD]|]. split; [apply U8; [lia|lia|exact NX]|]. split; [apply U8; [lia|lia|exact F0]|].
  split; [apply U8; [lia|lia|exact A0]|]. split; [apply U8; [lia|lia|exact F1]|]. split; [apply U8; [lia|lia|exact A1]|].
  intros i f a Hi. pose proof (nth_error_Some (ax_list e) i) as [Hs _].
  assert (Hlt : (i < length (ax_list e))%nat) by (apply Hs; rewrite Hi; discriminate).
  destruct (EXT i f a Hi) as (E1 & E2 & E3 & E4).
  split; [apply U8; [lia|lia|exact E1]|]. split; [apply U8; [lia|lia|exact E2]|].
  split; [apply U8; [lia|lia|exact E3]| apply U8; [lia|lia|exact E4]].
Qed.

Section FrameA.
Hypothesis WF : PMST.addrs_wf A.
Variables M M' : word -> option byte.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> PMST.dep A a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis RO : forall a, 65536 <= a < pa_rw_lo A -> M (Z_to_bv 64 a) = None -> M' (Z_to_bv 64 a) = None.

Lemma clear_dep lo hi : 0 <= lo -> hi < 2 ^ 47 -> (forall a, lo <= a < hi -> PMST.dep A a) -> L5.img_clear M lo hi -> L5.img_clear M' lo hi.
Proof. intros Hlo Hhi D C i Hi. rewrite AG; [apply C; exact Hi| lia| apply D; exact Hi]. Qed.
Lemma u8_dep a v : 0 <= a < 2 ^ 47 -> PMST.dep A a -> L5.u8_at segs M a v -> L5.u8_at segs M' a v.
Proof. intros Ha D. apply (L5C.u8_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG; [lia|]. replace i with a by lia. exact D. Qed.
Lemma u32_dep a v : 0 <= a < 2 ^ 47 -> (forall i, a <= i < a + 4 -> PMST.dep A i) -> L5.u32_at segs M a v -> L5.u32_at segs M' a v.
Proof.
  intros Ha D H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a); [exact H|lia|cbn; lia|].
  intros i Hi. apply AG; [cbn in Hi; lia|]. apply D. cbn in Hi. lia.
Qed.
Lemma u64_dep a v : 0 <= a < 2 ^ 47 -> (forall i, a <= i < a + 8 -> PMST.dep A i) -> L5.u64_at segs M a v -> L5.u64_at segs M' a v.
Proof. intros Ha D. apply (L5C.u64_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG; [lia|]. apply D. exact Hi. Qed.

Lemma err_okA_frame e : err_okA M e -> err_okA M' e.
Proof.
  pose proof (PMST.aw_errg A WF) as Heg. pose proof (PMST.aw_atexit A WF) as HX.
  intros (ERG & ATX). split.
  - destruct e.
    + apply u8_dep; [lia| apply PMST.in_foot_errg; lia| exact ERG].
    + apply (clear_dep (pa_errcat_guard A) (pa_errcat_guard A + 2)); [lia|lia| intros; apply PMST.in_foot_errg; lia| exact ERG].
  - apply (atexit_stA_agree WF M M' e); [|exact ATX]. intros i Hi. apply AG; [lia|]. apply PMST.in_foot_atexit. exact Hi.
Qed.

Lemma ls_okA_frame g : ls_okA g M -> ls_okA g M'.
Proof.
  intros ((RO0 & (can & Hcan & CAN) & NL & LL) & LOC & SYS & ERR).
  pose proof (PMST.aw_rw A WF) as Hrw. pose proof (PMST.aw_canary A WF) as Hcn. pose proof (PMST.aw_sysg A WF) as Hsg.
  pose proof (PMST.aw_gloc A WF) as Hgl. pose proof (PMST.aw_nl A WF) as Hnl. pose proof (PMST.aw_ll A WF) as Hll.
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + intros i Hi. apply RO; [exact Hi| apply RO0; exact Hi].
    + exists can. split; [exact Hcan|]. apply u64_dep; [lia| intros i Hi; right; left; exact Hi| exact CAN].
    + apply u8_dep; [lia| apply PMST.in_foot_nl; lia| exact NL].
    + apply u32_dep; [lia| intros i Hi; apply PMST.in_foot_ll; lia| exact LL].
  - unfold PMST.loc_ok in *. destruct (PMST.st_loc g).
    + destruct LOC as (G & P). destruct (PMST.aw_gloc_in A WF) as (iv & Hin & Hlo & Hhi). split.
      * apply u8_dep; [lia| apply (PMST.in_foot_loc A iv); [exact Hin| lia]| exact G].
      * apply u64_dep; [lia| intros i Hi; apply (PMST.in_foot_loc A iv); [exact Hin| lia]| exact P].
    + intros iv Hin. destruct (PMST.aw_locfoot A WF iv Hin) as [L1 L2].
      apply (clear_dep (fst iv) (snd iv)); [lia| lia| intros a Ha; apply (PMST.in_foot_loc A iv); assumption| apply LOC; exact Hin].
  - unfold PMST.sys_ok in *. destruct (PMST.st_sys g).
    + apply u8_dep; [lia| apply PMST.in_foot_sysg; lia| exact SYS].
    + apply (clear_dep (pa_syscat_guard A) (pa_syscat_guard A + 2)); [lia|lia| intros; apply PMST.in_foot_sysg; lia| exact SYS].
  - apply err_okA_frame. exact ERR.
Qed.
End FrameA.

Lemma pe_statics_exitA g M : ls_okA g M -> atexit_stA M (PMST.st_err g).
Proof. intros (_ & _ & _ & (_ & X)). exact X. Qed.
End Statics.
End PESTA.
