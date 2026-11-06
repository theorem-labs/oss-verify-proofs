(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk CellsX AStep Asn1Aux.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Tactic Notation "acallx" tactic3(apptac) :=
  lazymatch goal with
  | |- aevtM ?segs _ _ (MS _ _ _ _ _ ?m _) => eapply aevtM_cut_evt; [ eassumption | apptac | post_call segs m ]
  end.

Tactic Notation "acallx_sp" constr(e) tactic3(apptac) :=
  lazymatch goal with
  | |- aevtM ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      eapply aevtM_cut_evt;
      [ eassumption
      | apptac
      | lazymatch goal with |- forall x, ?P x -> _ => let h := head_of P in try unfold h end;
        rewrite ?(unsigned_lit e) by plia; post_call segs m ]
  end.

Lemma outside_dec : forall (W : list ivl) a, outside W a \/ ~ outside W a.
Proof.
  induction W as [|[lo hi] W IH]; intros a; cbn [outside]; [left; exact I|].
  destruct (IH a) as [H|H]; [| right; intros [_ H']; exact (H H')].
  destruct (Z_le_gt_dec lo a) as [H1|H1]; [destruct (Z_lt_ge_dec a hi) as [H2|H2]|].
  - right. intros [H3 _]. apply H3. lia.
  - left. split; [lia| exact H].
  - left. split; [lia| exact H].
Qed.

(* [comment removed for export] *)
Lemma HEAP_munch : forall segs L (HI : heap_iface segs L) h LB m m' mo (SP : Z) W,
  HEAP segs L HI h LB m mo -> alloc_ceiling <= SP ->
  munch W m m' -> wmono segs m m' ->
  (forall a, 0 <= a < 2^64 -> ~ outside W a -> client_waddr L LB SP (heap_top segs L HI h) a) ->
  HEAP segs L HI h LB m' mo.
Proof.
  intros segs L HI h LB m m' mo SP W HH HSP MU WM HW.
  eapply (heap_frame segs L HI); [exact HH| exact HSP| | exact WM].
  intros a Ha Hnc. destruct (outside_dec W a) as [Ho|Ho].
  - apply MU. rewrite wa_unsigned by lia. exact Ho.
  - exfalso. apply Hnc. apply HW; [exact Ha| exact Ho].
Qed.
