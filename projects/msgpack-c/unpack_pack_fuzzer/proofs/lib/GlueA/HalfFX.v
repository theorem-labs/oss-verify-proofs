(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import HalfC MemOps MemsetFX.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib HalfC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module HalfFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Fixpoint push_mem (E : env) (m : word -> option byte) (base : sv) (cells : list (int * sv)) : word -> option byte :=
  match cells with
  | [] => m
  | (off, v) :: tl => push_mem E (write_to_mem m (den E (sv_alu ALU_ADD base (VL (wlit off)))) (store_bytes 8%uint63 (den E v))) base tl
  end.

Lemma push_cells_sound : forall cells st base stn E ms mo,
  St.st_ok segs OPS E st ms mo -> s_resv st = RNone -> ms_resv ms = None ->
  push_cells segs st base cells = Some stn ->
  St.st_ok segs OPS E stn (ms_with_mem ms (push_mem E (ms_mem ms) base cells)) mo
  /\ s_pc stn = s_pc st /\ s_rf stn = s_rf st /\ s_ff stn = s_ff st /\ s_resv stn = RNone /\ s_facts stn = s_facts st
  /\ s_ops stn = s_ops st /\ s_priv stn = s_priv st /\ s_next stn = s_next st.
Proof.
  induction cells as [|[off v] tl IH]; intros st base stn E ms mo HS RV MRV H.
  - cbn [push_cells] in H. injection H as <-. cbn [push_mem].
    split; [exact (MemsetFX.st_ok_self segs OPS E st ms mo HS)|]. repeat split; try reflexivity. exact RV.
  - cbn [push_cells] in H. set (a := sv_alu ALU_ADD base (VL (wlit off))) in *.
    destruct (do_store segs st a 8%uint63 v) as [st'|] eqn:DS; [|discriminate H].
    unfold do_store in DS. destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate DS].
    destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate DS].
    destruct (okey o) as [key|] eqn:Hk; [|discriminate DS].
    destruct (can_write segs (s_facts st) (s_priv st) k r key 8%uint63) eqn:CW; [|discriminate DS].
    injection DS as <-. rewrite RV in H. cbn [resv_after_store] in H.
    assert (Hw : wok 8%uint63) by (right; right; right; reflexivity).
    destruct (store_sound segs OPS E st ms mo a k o r key 8%uint63 v RNone None HS Hw Ha Hr Hk CW eq_refl) as [SOK ST].
    replace (with_resv None (core_of ms)) with (core_of ms) in ST by (unfold with_resv, core_of; rewrite MRV; reflexivity).
    destruct (IH _ base stn E _ mo ST eq_refl MRV H) as (HS' & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    cbn [push_mem]. fold a. cbn [ms_mem ms_with_mem ms_upd] in HS'.
    split; [exact HS'|]. cbn [s_pc s_rf s_ff s_resv s_facts s_ops s_priv s_next] in F1, F2, F3, F5, F6, F7, F8. repeat split; assumption.
Qed.

Lemma write_same : forall bs (m : word -> option byte) A, 0 <= A -> A + Z.of_nat (length bs) <= two64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m (Z_to_bv 64 (A + i)) = nth_error bs (Z.to_nat i)) ->
  forall x, write_to_mem m (Z_to_bv 64 A) bs x = m x.
Proof.
  intros bs m A HA HB H x. pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX.
  rewrite <- (Z_to_bv_bv_unsigned _ x).
  destruct (Z_lt_le_dec (bv_unsigned x) A) as [Q|Q]; [apply write_to_mem_frame; unfold two64 in *; lia|].
  destruct (Z_lt_le_dec (bv_unsigned x) (A + Z.of_nat (length bs))) as [Q2|Q2]; [| apply write_to_mem_frame; unfold two64 in *; lia].
  replace (bv_unsigned x) with (A + (bv_unsigned x - A)) by lia.
  rewrite write_to_mem_in by lia. symmetry. apply H. lia.
Qed.

Lemma st_ok_regs_pc : forall E st ms ms' mo rf' (pc' nx : int),
  St.st_ok segs OPS E st ms mo ->
  ms_pc_val ms' = Z_to_bv 64 (to_Z pc') -> ms_fregs ms' = ms_fregs ms -> ms_svc_pending ms' = ms_svc_pending ms ->
  ms_resv ms' = ms_resv ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms -> ms_mem ms' = ms_mem ms ->
  rf_get rf' X0 = VL wzero ->
  (forall r, rget (Core (ms_regs ms') (ms_fregs ms') (ms_pc_val ms') (ms_fcsr ms') (ms_resv ms')) (reg_of_r5 r) = den E (rf_get rf' r)) ->
  St.st_ok segs OPS E (SS pc' rf' (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) nx) ms' mo.
Proof.
  intros E st ms ms' mo rf' pc' nx HS EPC EF ESV ERV EFC ERO EM X0' RG.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; rewrite ?EF, ?ESV, ?ERV, ?EFC, ?ERO, ?EM; try assumption.
Qed.

Fixpoint lookup_regs (l : list (r5 * sv)) (x : r5) (dflt : sv) : sv :=
  match l with
  | [] => dflt
  | (y, v) :: tl => lookup_regs tl x (if r5_eqb y x then v else dflt)
  end.

Lemma set_regs_fields : forall l st, s_pc (set_regs st l) = s_pc st /\ s_ff (set_regs st l) = s_ff st /\ s_resv (set_regs st l) = s_resv st
  /\ s_regs (set_regs st l) = s_regs st /\ s_facts (set_regs st l) = s_facts st /\ s_ops (set_regs st l) = s_ops st
  /\ s_priv (set_regs st l) = s_priv st /\ s_next (set_regs st l) = s_next st.
Proof.
  induction l as [|[y v] tl IH]; intros st; cbn [set_regs]; [repeat split; reflexivity|].
  destruct (IH (setr st y v)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8. unfold setr. destruct y; repeat split; reflexivity.
Qed.

Lemma set_regs_get : forall l st x, Forall (fun yv => fst yv <> X0) l ->
  rf_get (s_rf (set_regs st l)) x = lookup_regs l x (rf_get (s_rf st) x).
Proof.
  induction l as [|[y v] tl IH]; intros st x NZ; cbn [set_regs lookup_regs]; [reflexivity|].
  inversion NZ as [|? ? N1 N2]; subst. cbn [fst] in N1. rewrite (IH _ x N2). f_equal.
  assert (Hx : r5_eqb y X0 = false) by (destruct (r5_eqb y X0) eqn:Q; [apply r5_eqb_spec in Q; contradiction | reflexivity]).
  rewrite (setr_eq st y v Hx). cbn [s_rf].
  destruct (r5_eqb y x) eqn:Q.
  - apply r5_eqb_spec in Q. subst x. apply FI.rf_get_set_same.
  - apply FI.rf_get_set_other. intros ->. rewrite r5_eqb_refl in Q. discriminate Q.
Qed.

Lemma st_ok_set_regs_pc : forall E st ms ms' mo l (pc' : int),
  St.st_ok segs OPS E st ms mo ->
  ms_pc_val ms' = Z_to_bv 64 (to_Z pc') -> ms_fregs ms' = ms_fregs ms -> ms_svc_pending ms' = ms_svc_pending ms ->
  ms_resv ms' = ms_resv ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms -> ms_mem ms' = ms_mem ms ->
  Forall (fun yv => fst yv <> X0) l ->
  (forall r, rget (Core (ms_regs ms') (ms_fregs ms') (ms_pc_val ms') (ms_fcsr ms') (ms_resv ms')) (reg_of_r5 r)
             = den E (lookup_regs l r (rf_get (s_rf st) r))) ->
  St.st_ok segs OPS E (setpc (set_regs st l) pc') ms' mo.
Proof.
  intros E st ms ms' mo l pc' HS EPC EF ESV ERV EFC ERO EM NZ RG.
  destruct (set_regs_fields l st) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  assert (SH : setpc (set_regs st l) pc' = SS pc' (s_rf (set_regs st l)) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st)).
  { unfold setpc. rewrite A2, A3, A4, A5, A6, A7, A8. reflexivity. }
  rewrite SH. apply (st_ok_regs_pc E st ms ms' mo _ pc' (s_next st) HS EPC EF ESV ERV EFC ERO EM).
  - rewrite (set_regs_get l st X0 NZ).
    assert (K : forall l0 d, Forall (fun yv : r5 * sv => fst yv <> X0) l0 -> lookup_regs l0 X0 d = d).
    { induction l0 as [|[y v] tl IH]; intros d N0; cbn [lookup_regs]; [reflexivity|]. inversion N0 as [|? ? N1 N2]; subst. cbn [fst] in N1.
      rewrite (IH _ N2). destruct (r5_eqb y X0) eqn:Q; [apply r5_eqb_spec in Q; contradiction | reflexivity]. }
    rewrite (K l _ NZ). exact (so_x0 _ _ _ _ _ _ HS).
  - intros r. rewrite (set_regs_get l st r NZ). apply RG.
Qed.
End WithSegs.
End HalfFX.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib.
Import HalfC.TwinB MemOps.TwinB MemsetFX.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM PlanS CtrLib HalfC.TwinB.HalfC.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module HalfFX.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : St.optable.

Fixpoint push_mem (E : env) (m : word -> option byte) (base : sv) (cells : list (int * sv)) : word -> option byte :=
  match cells with
  | [] => m
  | (off, v) :: tl => push_mem E (write_to_mem m (den E (sv_alu ALU_ADD base (VL (wlit off)))) (store_bytes 8%uint63 (den E v))) base tl
  end.

Lemma push_cells_sound : forall cells st base stn E ms mo,
  St.st_ok segs OPS E st ms mo -> s_resv st = RNone -> ms_resv ms = None ->
  push_cells segs st base cells = Some stn ->
  St.st_ok segs OPS E stn (ms_with_mem ms (push_mem E (ms_mem ms) base cells)) mo
  /\ s_pc stn = s_pc st /\ s_rf stn = s_rf st /\ s_ff stn = s_ff st /\ s_resv stn = RNone /\ s_facts stn = s_facts st
  /\ s_ops stn = s_ops st /\ s_priv stn = s_priv st /\ s_next stn = s_next st.
Proof.
  induction cells as [|[off v] tl IH]; intros st base stn E ms mo HS RV MRV H.
  - cbn [push_cells] in H. injection H as <-. cbn [push_mem].
    split; [exact (MemsetFX.TwinB.MemsetFX.st_ok_self segs OPS E st ms mo HS)|]. repeat split; try reflexivity. exact RV.
  - cbn [push_cells] in H. set (a := sv_alu ALU_ADD base (VL (wlit off))) in *.
    destruct (do_store segs st a 8%uint63 v) as [st'|] eqn:DS; [|discriminate H].
    unfold do_store in DS. destruct (addr_of a) as [[k o]|] eqn:Ha; [|discriminate DS].
    destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate DS].
    destruct (okey o) as [key|] eqn:Hk; [|discriminate DS].
    destruct (can_write segs (s_facts st) (s_priv st) k r key 8%uint63) eqn:CW; [|discriminate DS].
    injection DS as <-. rewrite RV in H. cbn [resv_after_store] in H.
    assert (Hw : wok 8%uint63) by (right; right; right; reflexivity).
    destruct (store_sound segs OPS E st ms mo a k o r key 8%uint63 v RNone None HS Hw Ha Hr Hk CW eq_refl) as [SOK ST].
    replace (with_resv None (core_of ms)) with (core_of ms) in ST by (unfold with_resv, core_of; rewrite MRV; reflexivity).
    destruct (IH _ base stn E _ mo ST eq_refl MRV H) as (HS' & F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8).
    cbn [push_mem]. fold a. cbn [ms_mem ms_with_mem ms_upd] in HS'.
    split; [exact HS'|]. cbn [s_pc s_rf s_ff s_resv s_facts s_ops s_priv s_next] in F1, F2, F3, F5, F6, F7, F8. repeat split; assumption.
Qed.

Lemma write_same : forall bs (m : word -> option byte) A, 0 <= A -> A + Z.of_nat (length bs) <= two64 ->
  (forall i, 0 <= i < Z.of_nat (length bs) -> m (Z_to_bv 64 (A + i)) = nth_error bs (Z.to_nat i)) ->
  forall x, write_to_mem m (Z_to_bv 64 A) bs x = m x.
Proof.
  intros bs m A HA HB H x. pose proof (bv_unsigned_in_range _ x) as RX. unfold bv_modulus in RX.
  rewrite <- (Z_to_bv_bv_unsigned _ x).
  destruct (Z_lt_le_dec (bv_unsigned x) A) as [Q|Q]; [apply write_to_mem_frame; unfold two64 in *; lia|].
  destruct (Z_lt_le_dec (bv_unsigned x) (A + Z.of_nat (length bs))) as [Q2|Q2]; [| apply write_to_mem_frame; unfold two64 in *; lia].
  replace (bv_unsigned x) with (A + (bv_unsigned x - A)) by lia.
  rewrite write_to_mem_in by lia. symmetry. apply H. lia.
Qed.

Lemma st_ok_regs_pc : forall E st ms ms' mo rf' (pc' nx : int),
  St.st_ok segs OPS E st ms mo ->
  ms_pc_val ms' = Z_to_bv 64 (to_Z pc') -> ms_fregs ms' = ms_fregs ms -> ms_svc_pending ms' = ms_svc_pending ms ->
  ms_resv ms' = ms_resv ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms -> ms_mem ms' = ms_mem ms ->
  rf_get rf' X0 = VL wzero ->
  (forall r, rget (Core (ms_regs ms') (ms_fregs ms') (ms_pc_val ms') (ms_fcsr ms') (ms_resv ms')) (reg_of_r5 r) = den E (rf_get rf' r)) ->
  St.st_ok segs OPS E (SS pc' rf' (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) nx) ms' mo.
Proof.
  intros E st ms ms' mo rf' pc' nx HS EPC EF ESV ERV EFC ERO EM X0' RG.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  split; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; rewrite ?EF, ?ESV, ?ERV, ?EFC, ?ERO, ?EM; try assumption.
Qed.

Fixpoint lookup_regs (l : list (r5 * sv)) (x : r5) (dflt : sv) : sv :=
  match l with
  | [] => dflt
  | (y, v) :: tl => lookup_regs tl x (if r5_eqb y x then v else dflt)
  end.

Lemma set_regs_fields : forall l st, s_pc (set_regs st l) = s_pc st /\ s_ff (set_regs st l) = s_ff st /\ s_resv (set_regs st l) = s_resv st
  /\ s_regs (set_regs st l) = s_regs st /\ s_facts (set_regs st l) = s_facts st /\ s_ops (set_regs st l) = s_ops st
  /\ s_priv (set_regs st l) = s_priv st /\ s_next (set_regs st l) = s_next st.
Proof.
  induction l as [|[y v] tl IH]; intros st; cbn [set_regs]; [repeat split; reflexivity|].
  destruct (IH (setr st y v)) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  rewrite A1, A2, A3, A4, A5, A6, A7, A8. unfold setr. destruct y; repeat split; reflexivity.
Qed.

Lemma set_regs_get : forall l st x, Forall (fun yv => fst yv <> X0) l ->
  rf_get (s_rf (set_regs st l)) x = lookup_regs l x (rf_get (s_rf st) x).
Proof.
  induction l as [|[y v] tl IH]; intros st x NZ; cbn [set_regs lookup_regs]; [reflexivity|].
  inversion NZ as [|? ? N1 N2]; subst. cbn [fst] in N1. rewrite (IH _ x N2). f_equal.
  assert (Hx : r5_eqb y X0 = false) by (destruct (r5_eqb y X0) eqn:Q; [apply r5_eqb_spec in Q; contradiction | reflexivity]).
  rewrite (setr_eq st y v Hx). cbn [s_rf].
  destruct (r5_eqb y x) eqn:Q.
  - apply r5_eqb_spec in Q. subst x. apply FI.rf_get_set_same.
  - apply FI.rf_get_set_other. intros ->. rewrite r5_eqb_refl in Q. discriminate Q.
Qed.

Lemma st_ok_set_regs_pc : forall E st ms ms' mo l (pc' : int),
  St.st_ok segs OPS E st ms mo ->
  ms_pc_val ms' = Z_to_bv 64 (to_Z pc') -> ms_fregs ms' = ms_fregs ms -> ms_svc_pending ms' = ms_svc_pending ms ->
  ms_resv ms' = ms_resv ms -> ms_fcsr ms' = ms_fcsr ms -> ms_rom ms' = ms_rom ms -> ms_mem ms' = ms_mem ms ->
  Forall (fun yv => fst yv <> X0) l ->
  (forall r, rget (Core (ms_regs ms') (ms_fregs ms') (ms_pc_val ms') (ms_fcsr ms') (ms_resv ms')) (reg_of_r5 r)
             = den E (lookup_regs l r (rf_get (s_rf st) r))) ->
  St.st_ok segs OPS E (setpc (set_regs st l) pc') ms' mo.
Proof.
  intros E st ms ms' mo l pc' HS EPC EF ESV ERV EFC ERO EM NZ RG.
  destruct (set_regs_fields l st) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8).
  assert (SH : setpc (set_regs st l) pc' = SS pc' (s_rf (set_regs st l)) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st)).
  { unfold setpc. rewrite A2, A3, A4, A5, A6, A7, A8. reflexivity. }
  rewrite SH. apply (st_ok_regs_pc E st ms ms' mo _ pc' (s_next st) HS EPC EF ESV ERV EFC ERO EM).
  - rewrite (set_regs_get l st X0 NZ).
    assert (K : forall l0 d, Forall (fun yv : r5 * sv => fst yv <> X0) l0 -> lookup_regs l0 X0 d = d).
    { induction l0 as [|[y v] tl IH]; intros d N0; cbn [lookup_regs]; [reflexivity|]. inversion N0 as [|? ? N1 N2]; subst. cbn [fst] in N1.
      rewrite (IH _ N2). destruct (r5_eqb y X0) eqn:Q; [apply r5_eqb_spec in Q; contradiction | reflexivity]. }
    rewrite (K l _ NZ). exact (so_x0 _ _ _ _ _ _ HS).
  - intros r. rewrite (set_regs_get l st r NZ). apply RG.
Qed.
End WithSegs.
End HalfFX.
End TwinB.
