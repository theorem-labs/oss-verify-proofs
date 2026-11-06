(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec SCPS Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import RT_wf RT_rep CJ_iface RT_art RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RTW_sec_dstate.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RTW_sec_dstate.RT_fresh.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Section CeilWrap.
Context {ACEIL : Ceil}.

Definition fresh_x24 (st : rtstate) : Prop :=
  forall c, 0 <= c < KNUMCLASSES -> c <> 24 -> fresh_cls st c.

Definition ADRVd (k : nat) (m : word -> option byte) (mo : Model) (g : lghost) : Prop :=
  k = 0%nat \/ (forall st, RTREP st m -> RTWF st -> fresh_x24 st).

Lemma adrvd_weaken : forall k k' m mo g, ADRVd k m mo g -> (k' <= k)%nat -> ADRVd k' m mo g.
Proof. intros k k' m mo g [->|H] Hle; [left; lia| right; exact H]. Qed.

Lemma adrvd_model : forall k m mo mo' g, ADRVd k m mo g ->
  m_vmmaps mo' = m_vmmaps mo -> m_vm_lazy mo' = m_vm_lazy mo -> m_halted mo' = None -> ADRVd k m mo' g.
Proof. intros k m mo mo' g H _ _ _. exact H. Qed.

Lemma adrvd_g : forall k m mo g mo' g', ADRVd k m mo g -> ADRVd k m mo' g'.
Proof. intros k m mo g mo' g' H. exact H. Qed.

(* [comment removed for export] *)
Lemma adrvd_use : forall k m mo g st, ADRVd (S k) m mo g -> RTREP st m -> RTWF st -> fresh_x24 st.
Proof. intros k m mo g st [E|H] HR WF; [discriminate| exact (H st HR WF)]. Qed.

(* [comment removed for export] *)
Lemma adrvd_keep : forall k m' mo' g' st', RTREP st' m' -> RTWF st' -> fresh_x24 st' -> ADRVd k m' mo' g'.
Proof.
  intros k m' mo' g' st' HR' WF' HF. right. intros st'' HR'' WF'' c Hc H24.
  exact (agree_fresh st' st'' m' HR' WF' HR'' WF'' c Hc (HF c Hc H24)).
Qed.

Lemma adrvd_zero : forall m mo g, ADRVd 0 m mo g.
Proof. intros. left. reflexivity. Qed.

(* [comment removed for export] *)
Lemma adrvd_of_afreshd0 : forall k m mo g, AFRESHd 0 m mo g -> ADRVd k m mo g.
Proof.
  intros k m mo g H. right. intros st HR WF c Hc _. apply (H st HR WF c Hc).
  unfold KNUMCLASSES in Hc. destruct (Z.eq_dec c 0) as [->|]; [cbn; lia|]. pose proof (csize_pos c ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Theorem adrvd_frame : forall k sp0 SPB LB LF TRS B m m' mo g W,
  ARTd sp0 SPB LB LF TRS B m mo g -> ADRVd k m mo g -> munch W m m' -> wmono asegs m m' ->
  Forall (cj_write_ok sp0 SPB LB LF) W -> ADRVd k m' mo g.
Proof.
  intros k sp0 SPB LB LF TRS B m m' mo g W HA [->|HF] MU WM FW; [left; reflexivity|].
  destruct HA as (st & HR & WF & HM & HO & HB & HG & HFR & Hsp0 & HLB & HLF & HTRS & HQ & HB0 & HB1 & HSPB & HSW).
  assert (HR' : RTREP st m').
  { set (W' := List.filter (fun iv : Z * Z => fst iv <? snd iv) W).
    eapply (RTREP_frame st WF sp0 SPB W' m m'); try assumption.
    - rewrite Hsp0. exact HSPB.
    - subst LB LF. unfold W'. apply Forall_forall. intros iv Hiv. apply filter_In in Hiv as [Hiv _]. rewrite Forall_forall in FW. apply FW. exact Hiv.
    - unfold W'. apply Forall_forall. intros [lo hi] Hiv. apply filter_In in Hiv as [_ Hb]. cbn in Hb |- *. apply Z.ltb_lt. exact Hb.
    - apply munch_nonempty. exact MU. }
  eapply adrvd_keep; [exact HR'| exact WF| exact (HF st HR WF)].
Qed.

(* [comment removed for export] *)
Lemma live_bytes_nonneg' : forall l, 0 <= live_bytes l.
Proof. induction l as [|[a sz] l IH]; cbn; [lia|]. pose proof (bv_unsigned_in_range 64 sz). lia. Qed.
Lemma g_res_le_limit : forall st mo g, BINV mo g -> RTMODEL st mo -> g_res g <= 2^39.
Proof.
  intros st mo g (_ & _ & HB) HM. destruct HM as (_ & _ & _ & _ & _ & _ & _ & M8 & _).
  rewrite M8 in HB. unfold target_alloc_limit in HB. pose proof (npages_nonneg (g_win g)).
  unfold eager_used in HB. pose proof (live_bytes_nonneg' (maps_subtract_all (vm_backed_maps (m_vmmaps mo)) (m_vm_lazy mo))). lia.
Qed.

End CeilWrap.
