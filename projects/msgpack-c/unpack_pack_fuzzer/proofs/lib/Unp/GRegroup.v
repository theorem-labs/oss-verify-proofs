(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import GLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UG.
Open Scope Z_scope.

Module GRegroup.
Section Regroup.
Variable segs : list Segment.
Variable OPS : optable.

Definition rng (E : env) (k : int) (r : region) (a : Z) : Prop :=
  bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r.

Definition regroup (st : sstate) (KS : list int) (NR : list (int * region)) (NF : list fact) (nx : int) : sstate :=
  SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (add_regions NR (remove_keys KS (s_regs st))) (NF ++ s_facts st) (s_ops st) (s_priv st) nx.

Theorem regroup_sound : forall E st ms model KS NR NF nx,
  st_ok segs OPS E st ms model ->
  List.NoDup (map fst NR) ->
  (forall j rj, In (j, rj) NR -> PrimInt63.eqb j 0%uint63 = false /\ (In j KS \/ IMap.find j (s_regs st) = None)) ->
  (forall k, In k KS -> PrimInt63.eqb k 0%uint63 = false) ->

  (forall j rj, In (j, rj) NR -> region_ok segs (s_priv st) E (ms_mem ms) j rj) ->
  (forall j rj a, In (j, rj) NR -> rng E j rj a ->
      exists k r, In k KS /\ IMap.find k (s_regs st) = Some r /\ rng E k r a /\ (rg_w rj = true -> rg_w r = true)) ->

  (forall j1 r1 j2 r2 a, In (j1, r1) NR -> In (j2, r2) NR -> j1 <> j2 -> ~ (rng E j1 r1 a /\ rng E j2 r2 a)) ->
  Forall (fact_holds E) NF ->
  st_ok segs OPS E (regroup st KS NR NF nx) ms model.
Proof.
  intros E st ms model KS NR NF nx HS ND KEYS KS0 ROK COV PAIR HNF.
  destruct HS as [Qpc Qx0 Qregs Qfregs Qsvc Qresv Qfcsr Qrom Qz Qbst Qreg Qdisj Qpub Qfacts Qops Qapart Qmf Qcov Qminv].
  assert (BR : IMap.bst (remove_keys KS (s_regs st))) by (apply remove_keys_bst; exact Qbst).
  assert (FIND : forall j rj, IMap.find j (add_regions NR (remove_keys KS (s_regs st))) = Some rj ->
            In (j, rj) NR \/ (~ In j (map fst NR) /\ ~ In j KS /\ IMap.find j (s_regs st) = Some rj)).
  { intros j rj F. apply (find_add_regions NR _ j rj BR ND) in F as [F|[NI F]]; [left; exact F|].
    apply (find_remove_keys KS _ j rj Qbst) in F as [NK F]. right. auto. }
  assert (INB : forall a, in_based E (add_regions NR (remove_keys KS (s_regs st))) a -> in_based E (s_regs st) a).
  { intros a (j & rj & F & J0 & Ha). destruct (FIND j rj F) as [IN|(_ & _ & F0)].
    - destruct (COV j rj a IN Ha) as (k & r & Hk & Fk & Rk & _). exists k, r. split; [exact Fk|]. split; [exact (KS0 k Hk)| exact Rk].
    - exists j, rj. auto. }
  unfold regroup. constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply add_regions_bst. exact BR.
  - intros j rj F. destruct (FIND j rj F) as [IN|(_ & _ & F0)]; [exact (ROK j rj IN)| exact (Qreg j rj F0)].
  - intros k1 r1 k2 r2 F1 F2 NE Z1 Z2 W a [A1 A2].
    destruct (FIND k1 r1 F1) as [IN1|(NI1 & NK1 & G1)]; destruct (FIND k2 r2 F2) as [IN2|(NI2 & NK2 & G2)].
    + exact (PAIR k1 r1 k2 r2 a IN1 IN2 NE (conj A1 A2)).
    + destruct (COV k1 r1 a IN1 A1) as (k & r & Hk & Fk & Rk & Wk).
      assert (KN : k <> k2) by (intros ->; exact (NK2 Hk)).
      apply (Qdisj k r k2 r2 Fk G2 KN (KS0 k Hk) Z2 ltac:(destruct W as [W|W]; [left; exact (Wk W)| right; exact W]) a). split; [exact Rk| exact A2].
    + destruct (COV k2 r2 a IN2 A2) as (k & r & Hk & Fk & Rk & Wk).
      assert (KN : k1 <> k) by (intros ->; exact (NK1 Hk)).
      apply (Qdisj k1 r1 k r G1 Fk KN Z1 (KS0 k Hk) ltac:(destruct W as [W|W]; [left; exact W| right; exact (Wk W)]) a). split; [exact A1| exact Rk].
    + exact (Qdisj k1 r1 k2 r2 G1 G2 NE Z1 Z2 W a (conj A1 A2)).
  - intros r0 g gr c F0. apply (Qpub r0 g gr c).
    destruct (FIND 0%uint63 r0 F0) as [IN|(_ & _ & G0)]; [| exact G0].
    exfalso. destruct (KEYS _ _ IN) as [Z0 _]. discriminate Z0.
  - apply Forall_app. split; [exact HNF| exact Qfacts].
  - unfold ops_apart in *. apply (Forall_impl _ (P := fun o0 => forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o0) (map (den E) (op_args o0))) ->
                             ~ in_based E (s_regs st) a /\ ((exists seg, find_segment segs a 1 = Some seg) -> in_priv (s_priv st) a))); [|exact Qapart].
    intros o0 H a Ex. destruct (H a Ex) as [NBa P]. split; [intros IB; apply NBa, INB; exact IB| exact P].
  - intros a FA. apply Qcov. destruct FA as [IB|SEG]; [left; apply INB; exact IB| right; exact SEG].
Qed.
End Regroup.
End GRegroup.
