(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS.
Open Scope Z_scope.
Unset Lia Cache.

Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Lemma option_eq_dec_byte : forall (x y : option byte), {x = y} + {x <> y}.
Proof.
  intros [a|] [b|]; try (right; discriminate); [| left; reflexivity].
  destruct (bv_eqb a b) eqn:Q; [left; f_equal; unfold bv_eqb in Q; apply Z.eqb_eq in Q; apply bv_eq; exact Q| right].
  intros X. injection X as ->. unfold bv_eqb in Q. rewrite Z.eqb_refl in Q. discriminate Q.
Qed.

Lemma st_ok_based_replace_g : forall E st (R F : _) pc fc rv m m' rom mo kd rd rd',
  St.st_ok segs OPS E st (MS R F pc fc rv m rom) mo ->
  IMap.find kd (s_regs st) = Some rd -> PrimInt63.eqb kd 0%uint63 = false ->
  (forall a, 0 <= a < two64 ->
     (bv_unsigned (ev E kd) + loZ rd' <= a < bv_unsigned (ev E kd) + hiZ E rd' \/ m' (Z_to_bv 64 a) <> m (Z_to_bv 64 a)) ->
     (forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kd -> PrimInt63.eqb k2 0%uint63 = false ->
        ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2))
     /\ find_segment segs a 1 = None
     /\ (forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o))))) ->
  (forall x, m x <> None -> m' x <> None) ->
  (forall x b, m' x = Some b -> forall seg, find_segment segs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true) ->
  St.region_ok segs (s_priv st) E m' kd rd' ->
  (forall a, bv_unsigned (ev E kd) + loZ rd' <= a < bv_unsigned (ev E kd) + hiZ E rd' -> St.op_cov OPS (St.insts E (s_ops st)) a) ->
  St.st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add kd rd' (s_regs st)) (s_facts st) (s_ops st) (s_priv st) (s_next st))
           (MS R F pc fc rv m' rom) mo.
Proof.
  intros E st R F pc fc rv m m' rom mo kd rd rd' HS Hkd K ZONE MONO MINV RO' COVNEW.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *.
  assert (FIND : forall k r, IMap.find k (IMap.add kd rd' (s_regs st)) = Some r -> (k = kd /\ r = rd') \/ (k <> kd /\ IMap.find k (s_regs st) = Some r)).
  { intros k r H. destruct (Uint63.eqb kd k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in H by exact Pbst. injection H as <-. left; auto.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact Pbst || exact Q). right. split; [congruence| exact H]. }
  assert (SAME : forall a, 0 <= a < two64 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) \/
            ((forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kd -> PrimInt63.eqb k2 0%uint63 = false ->
                 ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2))
             /\ find_segment segs a 1 = None
             /\ (forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o)))))).
  { intros a Ha. destruct (option_eq_dec_byte (m' (Z_to_bv 64 a)) (m (Z_to_bv 64 a))) as [E1|NE]; [left; exact E1| right; apply (ZONE a Ha); right; exact NE]. }
  assert (OTHER : forall k r a, IMap.find k (s_regs st) = Some r -> k <> kd -> 0 <= a < two64 ->
            (PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r) ->
            (PrimInt63.eqb k 0%uint63 = true -> (exists seg, find_segment segs a 1 = Some seg) /\ ~ in_priv (s_priv st) a) ->
            m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros k r a Hk NK Ha BR AR. destruct (SAME a Ha) as [E1|(NB & NS & _)]; [exact E1| exfalso].
    destruct (Uint63.eqb k 0%uint63) eqn:K0.
    - destruct (AR eq_refl) as [[seg Hs] _]. rewrite NS in Hs. discriminate Hs.
    - exact (NB k r Hk NK K0 (BR eq_refl)). }
  assert (REGS : forall k r, IMap.find k (IMap.add kd rd' (s_regs st)) = Some r -> St.region_ok segs (s_priv st) E m' k r).
  { intros k r H. destruct (FIND k r H) as [[-> ->]|[NK Hk]]; [exact RO'|].
    apply (region_ok_frame segs (s_priv st) E m m' k r Pz (Preg k r Hk)). intros a Ha BR AR. exact (OTHER k r a Hk NK Ha BR AR). }
  pose proof (ro_range _ _ _ _ _ _ RO' K) as [RL' RH'].
  constructor; cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.bst_add. exact Pbst.
  - intros k1 q1 k2 q2 H1 H2 NE K1 K2 WW a [X1 X2].
    destruct (FIND k1 q1 H1) as [[-> ->]|[N1 G1]]; destruct (FIND k2 q2 H2) as [[-> ->]|[N2 G2]].
    + exact (NE eq_refl).
    + destruct (ZONE a ltac:(lia) (or_introl X1)) as (NB & _ & _). exact (NB k2 q2 G2 ltac:(congruence) K2 X2).
    + destruct (ZONE a ltac:(lia) (or_introl X2)) as (NB & _ & _). exact (NB k1 q1 G1 ltac:(congruence) K1 X1).
    + exact (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2 WW a (conj X1 X2)).
  - eapply pub_of_regions. exact REGS.
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Pops o Ho) as OH.
    apply (St.op_frame OPS _ _ m m' mo); [| intros a _ H; apply MONO; exact H| exact OH].
    intros a Ha FP. destruct (SAME a Ha) as [E1|(_ & _ & NF)]; [symmetry; exact E1| exfalso; exact (NF o Ho FP)].
  - apply Forall_forall. intros o Ho a FP. pose proof (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB PR]. split; [| exact PR].
    intros (k & r & H & K' & RG). destruct (FIND k r H) as [[-> ->]|[NK Hk]].
    + pose proof (bv_unsigned_in_range 64 (ev E kd)) as RK. rewrite bv_modulus_64 in RK.
      destruct (ZONE a ltac:(lia) (or_introl RG)) as (_ & _ & NF). exact (NF o Ho FP).
    + apply NB. exists k, r. auto.
  -
    intros a [(k & r & H & K' & RG)|SEG].
    + destruct (FIND k r H) as [[-> ->]|[NK Hk]]; [exact (COVNEW a RG)|]. apply Pcov. left. exists k, r. auto.
    + apply Pcov. right. exact SEG.
Qed.
End WithSegs.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS.
Open Scope Z_scope.
Unset Lia Cache.

Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Lemma option_eq_dec_byte : forall (x y : option byte), {x = y} + {x <> y}.
Proof.
  intros [a|] [b|]; try (right; discriminate); [| left; reflexivity].
  destruct (bv_eqb a b) eqn:Q; [left; f_equal; unfold bv_eqb in Q; apply Z.eqb_eq in Q; apply bv_eq; exact Q| right].
  intros X. injection X as ->. unfold bv_eqb in Q. rewrite Z.eqb_refl in Q. discriminate Q.
Qed.

Lemma st_ok_based_replace_g : forall E st (R F : _) pc fc rv m m' rom mo kd rd rd',
  St.st_ok segs OPS E st (MS R F pc fc rv m rom) mo ->
  IMap.find kd (s_regs st) = Some rd -> PrimInt63.eqb kd 0%uint63 = false ->
  (forall a, 0 <= a < two64 ->
     (bv_unsigned (ev E kd) + loZ rd' <= a < bv_unsigned (ev E kd) + hiZ E rd' \/ m' (Z_to_bv 64 a) <> m (Z_to_bv 64 a)) ->
     (forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kd -> PrimInt63.eqb k2 0%uint63 = false ->
        ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2))
     /\ find_segment segs a 1 = None
     /\ (forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o))))) ->
  (forall x, m x <> None -> m' x <> None) ->
  (forall x b, m' x = Some b -> forall seg, find_segment segs (bv_unsigned x) 1 = Some seg -> seg_writable seg = true) ->
  St.region_ok segs (s_priv st) E m' kd rd' ->
  (forall a, bv_unsigned (ev E kd) + loZ rd' <= a < bv_unsigned (ev E kd) + hiZ E rd' -> St.op_cov OPS (St.insts E (s_ops st)) a) ->
  St.st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (IMap.add kd rd' (s_regs st)) (s_facts st) (s_ops st) (s_priv st) (s_next st))
           (MS R F pc fc rv m' rom) mo.
Proof.
  intros E st R F pc fc rv m m' rom mo kd rd rd' HS Hkd K ZONE MONO MINV RO' COVNEW.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending] in *.
  assert (FIND : forall k r, IMap.find k (IMap.add kd rd' (s_regs st)) = Some r -> (k = kd /\ r = rd') \/ (k <> kd /\ IMap.find k (s_regs st) = Some r)).
  { intros k r H. destruct (Uint63.eqb kd k) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k. rewrite IMap.find_add_same in H by exact Pbst. injection H as <-. left; auto.
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact Pbst || exact Q). right. split; [congruence| exact H]. }
  assert (SAME : forall a, 0 <= a < two64 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) \/
            ((forall k2 r2, IMap.find k2 (s_regs st) = Some r2 -> k2 <> kd -> PrimInt63.eqb k2 0%uint63 = false ->
                 ~ (bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2))
             /\ find_segment segs a 1 = None
             /\ (forall o, In o (s_ops st) -> ~ Exists (fun iv => fst iv <= a < snd iv) (St.op_fp OPS (op_id o) (map (den E) (op_args o)))))).
  { intros a Ha. destruct (option_eq_dec_byte (m' (Z_to_bv 64 a)) (m (Z_to_bv 64 a))) as [E1|NE]; [left; exact E1| right; apply (ZONE a Ha); right; exact NE]. }
  assert (OTHER : forall k r a, IMap.find k (s_regs st) = Some r -> k <> kd -> 0 <= a < two64 ->
            (PrimInt63.eqb k 0%uint63 = false -> bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r) ->
            (PrimInt63.eqb k 0%uint63 = true -> (exists seg, find_segment segs a 1 = Some seg) /\ ~ in_priv (s_priv st) a) ->
            m' (Z_to_bv 64 a) = m (Z_to_bv 64 a)).
  { intros k r a Hk NK Ha BR AR. destruct (SAME a Ha) as [E1|(NB & NS & _)]; [exact E1| exfalso].
    destruct (Uint63.eqb k 0%uint63) eqn:K0.
    - destruct (AR eq_refl) as [[seg Hs] _]. rewrite NS in Hs. discriminate Hs.
    - exact (NB k r Hk NK K0 (BR eq_refl)). }
  assert (REGS : forall k r, IMap.find k (IMap.add kd rd' (s_regs st)) = Some r -> St.region_ok segs (s_priv st) E m' k r).
  { intros k r H. destruct (FIND k r H) as [[-> ->]|[NK Hk]]; [exact RO'|].
    apply (region_ok_frame segs (s_priv st) E m m' k r Pz (Preg k r Hk)). intros a Ha BR AR. exact (OTHER k r a Hk NK Ha BR AR). }
  pose proof (ro_range _ _ _ _ _ _ RO' K) as [RL' RH'].
  constructor; cbn [MS ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  - apply IMap.bst_add. exact Pbst.
  - intros k1 q1 k2 q2 H1 H2 NE K1 K2 WW a [X1 X2].
    destruct (FIND k1 q1 H1) as [[-> ->]|[N1 G1]]; destruct (FIND k2 q2 H2) as [[-> ->]|[N2 G2]].
    + exact (NE eq_refl).
    + destruct (ZONE a ltac:(lia) (or_introl X1)) as (NB & _ & _). exact (NB k2 q2 G2 ltac:(congruence) K2 X2).
    + destruct (ZONE a ltac:(lia) (or_introl X2)) as (NB & _ & _). exact (NB k1 q1 G1 ltac:(congruence) K1 X1).
    + exact (Pdisj k1 q1 k2 q2 G1 G2 NE K1 K2 WW a (conj X1 X2)).
  - eapply pub_of_regions. exact REGS.
  - apply Forall_forall. intros o Ho. pose proof (proj1 (Forall_forall _ _) Pops o Ho) as OH.
    apply (St.op_frame OPS _ _ m m' mo); [| intros a _ H; apply MONO; exact H| exact OH].
    intros a Ha FP. destruct (SAME a Ha) as [E1|(_ & _ & NF)]; [symmetry; exact E1| exfalso; exact (NF o Ho FP)].
  - apply Forall_forall. intros o Ho a FP. pose proof (proj1 (Forall_forall _ _) Papart o Ho a FP) as [NB PR]. split; [| exact PR].
    intros (k & r & H & K' & RG). destruct (FIND k r H) as [[-> ->]|[NK Hk]].
    + pose proof (bv_unsigned_in_range 64 (ev E kd)) as RK. rewrite bv_modulus_64 in RK.
      destruct (ZONE a ltac:(lia) (or_introl RG)) as (_ & _ & NF). exact (NF o Ho FP).
    + apply NB. exists k, r. auto.
  -
    intros a [(k & r & H & K' & RG)|SEG].
    + destruct (FIND k r H) as [[-> ->]|[NK Hk]]; [exact (COVNEW a RG)|]. apply Pcov. left. exists k, r. auto.
    + apply Pcov. right. exact SEG.
Qed.
End WithSegs.
End TwinB.
