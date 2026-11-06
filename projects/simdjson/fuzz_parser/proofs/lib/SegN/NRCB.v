(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegTmpl SegGhost.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.SegN Require Import NRMG NRMV NRMC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import AX2. Import AX2S.
Open Scope Z_scope.

Module NRCB.
Local Notation u := bv_unsigned.

(* [comment removed for export] *)
Definition aug1 (s : sidecond) : list sidecond :=
  match s with
  | SCBr t BC_EQ (EAlu ALU_SLTU v x) (ELit 0) => [SCBr (negb t) BC_LTU v x]
  | SCBr t BC_NE (EAlu ALU_SLTU v x) (ELit 0) => [SCBr t BC_LTU v x]
  | _ => []
  end.
Definition augp (p : list sidecond) : list sidecond := p ++ flat_map aug1 p.
Definition augc (c : SG.vc) : SG.vc :=
  SG.VC (SG.vc_kn c) (augp (SG.vc_path c)) (SG.vc_log c) (SG.vc_src c) (SG.vc_tgt c) (SG.vc_facts c).
Definition nrcb_ok (segs : list Segment) (c : SG.vc) : bool := NRC.nrc_ok segs (augc c).

Section S.
Variable segs : list Segment.

Lemma sltu0 : forall E v x, u (edenot E (EAlu ALU_SLTU v x)) = 0 <-> u (edenot E x) <= u (edenot E v).
Proof.
  intros E v x. rewrite NRV.ue_sltu. destruct (u (edenot E v) <? u (edenot E x)) eqn:H.
  - apply Z.ltb_lt in H. split; intros; lia.
  - apply Z.ltb_ge in H. split; intros; lia.
Qed.

Lemma aug1_ok : forall m E s, sc_denot segs m E s -> Forall (sc_denot segs m E) (aug1 s).
Proof.
  intros m E s H. destruct s as [t c a b| | | | | | ]; cbn [aug1]; try (apply Forall_nil).
  destruct c; try (apply Forall_nil).
  all: destruct a as [| |op v x| | | | |]; try (apply Forall_nil).
  all: destruct op; try (apply Forall_nil).
  all: destruct b as [z| | | | | | |]; try (apply Forall_nil).
  all: destruct z; try (apply Forall_nil).
  all: apply Forall_cons; [|apply Forall_nil]; cbn [sc_denot branch_taken] in *; unfold bv_eqb, bv_ltu in *;
       pose proof (sltu0 E v x) as S; change (u (edenot E (ELit 0))) with 0 in H.
  - destruct t.
    + apply Z.eqb_eq in H. apply S in H. cbn [negb]. apply Z.ltb_ge. lia.
    + apply Z.eqb_neq in H. cbn [negb]. apply Z.ltb_lt.
      destruct (Z_le_gt_dec (u (edenot E x)) (u (edenot E v))) as [L|L]; [exfalso; apply H, S, L | lia].
  - destruct t.
    + apply negb_true_iff, Z.eqb_neq in H. apply Z.ltb_lt.
      destruct (Z_le_gt_dec (u (edenot E x)) (u (edenot E v))) as [L|L]; [exfalso; apply H, S, L | lia].
    + apply negb_false_iff, Z.eqb_eq in H. apply S in H. apply Z.ltb_ge. lia.
Qed.

Lemma augp_ok : forall m E p, scs_denot segs m E p -> scs_denot segs m E (augp p).
Proof.
  intros m E p H. unfold augp, scs_denot in *. apply Forall_app. split; [exact H|].
  apply Forall_flat_map. apply Forall_forall. intros s Hin. apply aug1_ok. exact (proj1 (Forall_forall _ _) H s Hin).
Qed.
End S.

Theorem nrcb_ok_sound : forall segs c, nrcb_ok segs c = true -> SG.vc_holds segs (SNU.snu_gp segs) c.
Proof.
  intros segs c H E m HK HP HL HS.
  exact (NRC.nrc_ok_sound segs (augc c) H E m HK (augp_ok segs m E _ HP) HL HS).
Qed.
End NRCB.
