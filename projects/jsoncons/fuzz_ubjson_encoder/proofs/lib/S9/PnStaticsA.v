(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PropExec StoreOk HeapIface LibIface L5Defs L5Core.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceABx.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PnLayout.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S9 Require Import PnStatics.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module PNSTA.
Section Statics.
Variable segs : list Segment.
Variable A : pm_addrs.
Variable AA : pm_asan_addrs.
Variable AN : PNL.pn_addrs.

Definition atexit_stA (M : word -> option byte) (ax : PNST.bax) : Prop :=
  HAJ.atexit_cells segs M (pa_atexit A) (paa_atexit_f0 AA) (paa_atexit_a0 AA) (PNL.pn_drv_call AN) (PNL.pn_drv_guard AN) (paa_at_cxa_atexit AA) (PNST.bax_list A AN ax).

Definition berr_okA (M : word -> option byte) (ax : PNST.bax) : Prop :=
  (if PNST.bax_cat ax then L5.u8_at segs M (pa_errcat_guard A) 1 else L5.img_clear M (pa_errcat_guard A) (pa_errcat_guard A + 2))
  /\ PNST.bdec_ok segs AN M (PNST.bax_dec ax) /\ atexit_stA M ax.

Definition ls_okA (g : PNST.st) (M : word -> option byte) : Prop :=
  PMSTA.base_okA segs A M /\ PMST.loc_ok segs A M (PNST.st_loc g) /\ PMST.sys_ok segs A M (PNST.st_sys g) /\ berr_okA M (PNST.st_ax g).

Definition TopLSA : lib_statics := {| ls_state := PNST.st; LibIface.ls_ok := ls_okA; ls_g0 := PNST.g0 |}.

Lemma atexit_stA_agree (WF : PMST.addrs_wf A) M M' ax :
  (forall i, pa_atexit A <= i < pa_atexit A + 544 -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i)) -> atexit_stA M ax -> atexit_stA M' ax.
Proof.
  intros AG. pose proof (PMST.aw_atexit A WF) as HX. unfold atexit_stA, HAJ.atexit_cells.
  assert (U8 : forall a v, pa_atexit A <= a -> a + 8 <= pa_atexit A + 544 -> L5.u64_at segs M a v -> L5.u64_at segs M' a v).
  { intros a v H1 H2. apply (L5C.u64_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG. lia. }
  assert (U4 : forall a v, pa_atexit A <= a -> a + 4 <= pa_atexit A + 544 -> L5.u32_at segs M a v -> L5.u32_at segs M' a v).
  { intros a v H1 H2 H. unfold L5.u32_at in *. rewrite (L5C.rdn_agree segs M M' 4%nat a); [exact H|lia|cbn; lia|]. intros i Hi. apply AG. cbn in Hi. lia. }
  assert (U1 : forall a v, pa_atexit A <= a -> a + 1 <= pa_atexit A + 544 -> L5.u8_at segs M a v -> L5.u8_at segs M' a v).
  { intros a v H1 H2. apply (L5C.u8_at_agree segs M M'); [|lia|lia]. intros i Hi. apply AG. lia. }
  assert (LEN : (length (PNST.bax_list A AN ax) <= 3)%nat) by (destruct ax; cbn; lia).
  intros (F & LK & SL & HD & NX & F0 & A0 & F1 & A1 & EXT).
  split; [apply U1; [lia|lia|exact F]|]. split; [apply U4; [lia|lia|exact LK]|]. split; [apply U4; [lia|lia|exact SL]|].
  split; [apply U8; [lia|lia|exact HD]|]. split; [apply U8; [lia|lia|exact NX]|]. split; [apply U8; [lia|lia|exact F0]|].
  split; [apply U8; [lia|lia|exact A0]|]. split; [apply U8; [lia|lia|exact F1]|]. split; [apply U8; [lia|lia|exact A1]|].
  intros i f a Hi. pose proof (nth_error_Some (PNST.bax_list A AN ax) i) as [Hs _].
  assert (Hlt : (i < length (PNST.bax_list A AN ax))%nat) by (apply Hs; rewrite Hi; discriminate).
  destruct (EXT i f a Hi) as (E1 & E2 & E3 & E4).
  split; [apply U8; [lia|lia|exact E1]|]. split; [apply U8; [lia|lia|exact E2]|].
  split; [apply U8; [lia|lia|exact E3]| apply U8; [lia|lia|exact E4]].
Qed.

Section FrameA.
Hypothesis WF : PNST.addrs_wf A AN.
Variables M M' : word -> option byte.
Hypothesis AG : forall a, 0 <= a < 2 ^ 64 -> PNST.dep A AN a -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a).
Hypothesis RO : forall a, 65536 <= a < pa_rw_lo A -> M (Z_to_bv 64 a) = None -> M' (Z_to_bv 64 a) = None.

Lemma berr_okA_frame ax : berr_okA M ax -> berr_okA M' ax.
Proof.
  pose proof (PMST.aw_errg A (PNST.aw_j A AN WF)) as Heg. pose proof (PMST.aw_atexit A (PNST.aw_j A AN WF)) as HX.
  intros (ERG & DEC & ATX). split; [|split].
  - destruct (PNST.bax_cat ax).
    + apply (PNST.u8_depB segs A AN M M' AG); [lia| apply PNST.dep_of_j, PMST.in_foot_errg; lia| exact ERG].
    + apply (PNST.clear_depB A AN M M' AG (pa_errcat_guard A) (pa_errcat_guard A + 2)); [lia|lia| intros; apply PNST.dep_of_j, PMST.in_foot_errg; lia| exact ERG].
  - exact (PNST.bdec_frame segs A AN WF M M' AG (PNST.bax_dec ax) DEC).
  - apply (atexit_stA_agree (PNST.aw_j A AN WF) M M' ax); [|exact ATX]. intros i Hi. apply AG; [lia|]. apply PNST.dep_of_j, PMST.in_foot_atexit. exact Hi.
Qed.

Lemma ls_okA_frame g : ls_okA g M -> ls_okA g M'.
Proof.
  intros ((RO0 & (can & Hcan & CAN) & NL & LL) & LOC & SYS & ERR).
  pose proof (PNST.aw_j A AN WF) as WJ.
  pose proof (PMST.aw_rw A WJ) as Hrw. pose proof (PMST.aw_canary A WJ) as Hcn. pose proof (PMST.aw_sysg A WJ) as Hsg.
  pose proof (PMST.aw_gloc A WJ) as Hgl. pose proof (PMST.aw_nl A WJ) as Hnl. pose proof (PMST.aw_ll A WJ) as Hll.
  split; [|split; [|split]].
  - split; [|split; [|split]].
    + intros i Hi. apply RO; [exact Hi| apply RO0; exact Hi].
    + exists can. split; [exact Hcan|]. apply (PNST.u64_depB segs A AN M M' AG); [lia| intros i Hi; right; left; exact Hi| exact CAN].
    + apply (PNST.u8_depB segs A AN M M' AG); [lia| apply PNST.dep_of_j, PMST.in_foot_nl; lia| exact NL].
    + apply (PNST.u32_depB segs A AN M M' AG); [lia| intros i Hi; apply PNST.dep_of_j, PMST.in_foot_ll; lia| exact LL].
  - unfold PMST.loc_ok in *. destruct (PNST.st_loc g).
    + destruct LOC as (G & P). destruct (PMST.aw_gloc_in A WJ) as (iv & Hin & Hlo & Hhi). split.
      * apply (PNST.u8_depB segs A AN M M' AG); [lia| apply PNST.dep_of_j, (PMST.in_foot_loc A iv); [exact Hin| lia]| exact G].
      * apply (PNST.u64_depB segs A AN M M' AG); [lia| intros i Hi; apply PNST.dep_of_j, (PMST.in_foot_loc A iv); [exact Hin| lia]| exact P].
    + intros iv Hin. destruct (PMST.aw_locfoot A WJ iv Hin) as [L1 L2].
      apply (PNST.clear_depB A AN M M' AG (fst iv) (snd iv)); [lia| lia| intros a Ha; apply PNST.dep_of_j, (PMST.in_foot_loc A iv); assumption| apply LOC; exact Hin].
  - unfold PMST.sys_ok in *. destruct (PNST.st_sys g).
    + apply (PNST.u8_depB segs A AN M M' AG); [lia| apply PNST.dep_of_j, PMST.in_foot_sysg; lia| exact SYS].
    + apply (PNST.clear_depB A AN M M' AG (pa_syscat_guard A) (pa_syscat_guard A + 2)); [lia|lia| intros; apply PNST.dep_of_j, PMST.in_foot_sysg; lia| exact SYS].
  - apply berr_okA_frame. exact ERR.
Qed.
End FrameA.

Lemma pn_statics_exitA g M : ls_okA g M -> atexit_stA M (PNST.st_ax g) /\ PNST.bdec_ok segs AN M (PNST.bax_dec (PNST.st_ax g)).
Proof. intros (_ & _ & _ & (_ & D & X)). split; [exact X| exact D]. Qed.
End Statics.
End PNSTA.
