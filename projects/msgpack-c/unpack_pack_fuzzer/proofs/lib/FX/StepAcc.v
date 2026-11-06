(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs MemProofs StepSoundBase StepSoundMem Acc.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step ValP MemP StepB StepM.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module StepAcc.
Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Definition acc_ok (E : env) (st : sstate) (a : word) (n : Z) : Prop :=
  forall j, 0 <= j < n -> fx_acc segs E (s_regs st) (bv_unsigned a + j).

Lemma access_acc0 : forall E R fs priv m a k o r key w,
  ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E fs -> region_ok segs priv E m k r -> wok w ->
  addr_of a = Some (k, o) -> IMap.find k R = Some r -> okey o = Some key ->
  can_read segs fs priv k r key w = true ->
  forall j, 0 <= j < to_Z w -> fx_acc segs E R (bv_unsigned (den E a) + j).
Proof.
  intros E R fs priv m a k o r key w Hz Hfs RO Hw Ha Hr Hk CR j Hj.
  pose proof (can_read_sound segs priv E m fs k r key w Hfs Hz RO Hw CR) as (RA & RAw & _ & RNG & ABS).
  cbv zeta in *.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  rewrite (access_addr E a k o key (addrZ E k key) Hz Ha Hk eq_refl RA ltac:(lia)).
  rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; unfold two64 in *; lia).
  destruct (PrimInt63.eqb k 0%uint63) eqn:K.
  - right. destruct (ABS eq_refl j Hj) as [[bs M] _].
    apply (memory_read_find_segment segs (addrZ E k key + j) bs); [unfold two64 in *; lia| exact M].
  - left. exists k, r. split; [exact Hr|]. split; [exact K|]. pose proof (RNG eq_refl j Hj). unfold addrZ. lia.
Qed.

Lemma access_acc : forall E st ms model a k o r key w,
  st_ok segs OPS E st ms model -> wok w ->
  addr_of a = Some (k, o) -> IMap.find k (s_regs st) = Some r -> okey o = Some key ->
  can_read segs (s_facts st) (s_priv st) k r key w = true ->
  acc_ok E st (den E a) (to_Z w).
Proof.
  intros E st ms model a k o r key w HS Hw Ha Hr Hk CR.
  exact (access_acc0 E (s_regs st) (s_facts st) (s_priv st) (ms_mem ms) a k o r key w (so_zero _ _ _ _ _ _ HS) (so_facts _ _ _ _ _ _ HS)
           (so_reg _ _ _ _ _ _ HS k r Hr) Hw Ha Hr Hk CR).
Qed.

Lemma do_load_acc : forall E st ms model a w sx v,
  st_ok segs OPS E st ms model -> wok w ->
  do_load segs st a w sx = inl (Some v) ->
  acc_ok E st (den E a) (to_Z w).
Proof.
  intros E st ms model a w sx v HS Hw H. unfold do_load in H.
  pose proof (so_zero _ _ _ _ _ _ HS) as Hz. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  assert (Hw8 : 1 <= to_Z w <= 8) by (unfold wok in Hw; lia).
  destruct (addr_of a) as [[k o]|] eqn:Ha.
  - destruct (IMap.find k (s_regs st)) as [r|] eqn:Hr; [|discriminate].
    destruct (okey o) as [key|] eqn:Hk; [|discriminate].
    destruct (can_read segs (s_facts st) (s_priv st) k r key w) eqn:CR; [|discriminate].
    exact (access_acc E st ms model a k o r key w HS Hw Ha Hr Hk CR).
  - destruct (sym_addr_of (s_regs st) a) as [[[k r] off]|] eqn:SA; [|discriminate].
    destruct (sym_addr_of_sound E (s_regs st) a k r off SA) as [Hr Da].
    pose proof (so_reg _ _ _ _ _ _ HS k r Hr) as RO.
    assert (X : PrimInt63.eqb k 0%uint63 = false /\ 0 <= bv_unsigned (ev E k) + bv_unsigned (den E off)
                /\ bv_unsigned (ev E k) + bv_unsigned (den E off) + to_Z w <= two64
                /\ loZ r = 0 /\ bv_unsigned (den E off) + to_Z w <= hiZ E r).
    { destruct (can_read_sym (s_facts st) k r off w) as [jb|] eqn:CS.
      - destruct (can_read_sym_sound E (s_facts st) k r off w jb Hfs CS) as (K & RC & BG & LO & _ & HI).
        destruct (sym_load_sound segs (s_priv st) E (ms_mem ms) k r off w sx jb Hz RO K RC BG LO Hw8 HI) as (RA & RAw & _). auto.
      -
        destruct (can_read_symz (s_facts st) k r off w) eqn:CZ; [|discriminate].
        destruct (can_read_symz_sound E (s_facts st) k r off w Hfs CZ) as (K & RC & BG & LO & _ & HI).
        destruct (symz_load_sound segs (s_priv st) E (ms_mem ms) k r off w sx Hz RO K RC BG LO Hw8 HI) as (RA & RAw & _). auto. }
    destruct X as (K & RA & RAw & LO & HI).
    intros j Hj. left. exists k, r. split; [exact Hr|]. split; [exact K|].
    rewrite Da, bv_add_unsigned. unfold bv_wrap. rewrite bv_modulus_64.
    pose proof (bv_unsigned_in_range 64 (den E off)) as RU. rewrite bv_modulus_64 in RU.
    rewrite Z.mod_small by (unfold two64 in *; lia). lia.
Qed.

Lemma do_store_acc0 : forall E st m a w v st',
  ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E (s_facts st) ->
  (forall k r, IMap.find k (s_regs st) = Some r -> region_ok segs (s_priv st) E m k r) -> wok w ->
  do_store segs st a w v = inl st' ->
  acc_ok E st (den E a) (to_Z w).
Proof.
  intros E st m a w v st' Hz Hfs Hreg Hw DS.
  destruct (do_store_inv segs st a w v st' DS) as (k & o & r & key & Ha & Hr & Hk & CW & _).
  pose proof (Hreg k r Hr) as RO.
  destruct (can_write_sound segs (s_priv st) E m (s_facts st) k r key w Hfs Hz RO Hw CW) as (CR & _).
  exact (access_acc0 E (s_regs st) (s_facts st) (s_priv st) m a k o r key w Hz Hfs RO Hw Ha Hr Hk CR).
Qed.

Lemma do_store_acc : forall E st ms model a w v st',
  st_ok segs OPS E st ms model -> wok w ->
  do_store segs st a w v = inl st' ->
  acc_ok E st (den E a) (to_Z w).
Proof.
  intros E st ms model a w v st' HS Hw DS.
  exact (do_store_acc0 E st (ms_mem ms) a w v st' (so_zero _ _ _ _ _ _ HS) (so_facts _ _ _ _ _ _ HS) (so_reg _ _ _ _ _ _ HS) Hw DS).
Qed.

Definition ranges_ok (E : env) (st : sstate) (rs : list (word * nat)) : Prop :=
  Forall (fun an => acc_ok E st (fst an) (Z.of_nat (snd an))) rs.

Lemma wok4 : wok 4%uint63. Proof. unfold wok. right; right; left; reflexivity. Qed.
Lemma wok8 : wok 8%uint63. Proof. unfold wok. right; right; right; reflexivity. Qed.

Lemma interp_acc_EDone : forall c m report,
  interp_eff_accesses segs (EDone c) m = MachineOk report -> @accessed_ranges _ report = [].
Proof. intros c m report H. cbn in H. injection H as <-. reflexivity. Qed.

Theorem exec_acc : forall i fi E st ms model st' report,
  st_ok segs OPS E st ms model -> of_instr i = Some fi -> exec segs fi st = XOk st' ->
  interp_eff_accesses segs (Sem.exec (Z_to_bv 64 4) i (core_of ms)) (ms_mem ms) = MachineOk report ->
  ranges_ok E st (@accessed_ranges _ report).
Proof.
  intros i fi E st ms model st' report HS Hof Hx HI.
  pose proof (Acc.interp_accs_in segs _ _ _ _ (Acc.exec_accs (Z_to_bv 64 4) i (core_of ms)) HI) as FA.
  unfold ranges_ok.
  destruct i; cbn [Acc.mem_acc] in FA;
    try (eapply Forall_impl; [|exact FA]; intros an F; contradiction).
  -
    unfold of_instr in Hof. destruct (r5_of_reg rd) as [d|] eqn:Hrd; [|discriminate]. destruct (r5_of_reg rs1) as [s|] eqn:Hrs1; [|discriminate].
    injection Hof as <-. cbn [exec] in Hx.
    destruct (do_load segs st (sv_alu ALU_ADD (getr st s) (VL (w_of_imm imm))) (Step.msize_bytes sz) signed) as [[v|]|why] eqn:DL; try discriminate.
    eapply Forall_impl; [|exact FA]. intros [a n] [X1 X2]. cbn [fst snd] in *. subst a n.
    rewrite (ea_den segs OPS E st ms model s rs1 _ imm HS Hrs1).
    pose proof (do_load_acc E st ms model _ _ _ v HS (msize_wok sz) DL) as ACC.
    replace (Z.of_nat (Acc.msz_nat sz)) with (to_Z (Step.msize_bytes sz)) by (destruct sz; reflexivity). exact ACC.
  -
    unfold of_instr in Hof. destruct (r5_of_reg rs1) as [s|] eqn:Hrs1; [|discriminate]. destruct (r5_of_reg rs2) as [s2|] eqn:Hrs2; [|discriminate].
    injection Hof as <-. cbn [exec] in Hx.
    destruct (do_store segs st (sv_alu ALU_ADD (getr st s) (VL (w_of_imm imm))) (Step.msize_bytes sz) (getr st s2)) as [st1|why] eqn:DS; [|discriminate].
    eapply Forall_impl; [|exact FA]. intros [a n] [X1 X2]. cbn [fst snd] in *. subst a n.
    rewrite (ea_den segs OPS E st ms model s rs1 _ imm HS Hrs1).
    pose proof (do_store_acc E st ms model _ _ _ st1 HS (msize_wok sz) DS) as ACC.
    replace (Z.of_nat (Acc.msz_nat sz)) with (to_Z (Step.msize_bytes sz)) by (destruct sz; reflexivity). exact ACC.
  -
    unfold of_instr in Hof. destruct (r5_of_reg rd) as [d|] eqn:Hrd; [|discriminate]. destruct (r5_of_reg rs1) as [s|] eqn:Hrs1; [|discriminate].
    injection Hof as <-. cbn [exec] in Hx.
    destruct (aligned (s_facts st) (getr st s) (awidth_log w)) eqn:AL; [|discriminate].
    destruct (do_load segs st (getr st s) (awidth_bytes w) true) as [[v|]|why] eqn:DL; try discriminate.
    eapply Forall_impl; [|exact FA]. intros [a n] [X1 X2]. cbn [fst snd] in *. subst a n.
    rewrite (getr_den segs OPS E st ms model s rs1 HS Hrs1).
    pose proof (do_load_acc E st ms model _ _ _ v HS (awidth_wok w) DL) as ACC.
    replace (Z.of_nat (Acc.aw_nat w)) with (to_Z (awidth_bytes w)) by (destruct w; reflexivity). exact ACC.
  -
    unfold of_instr in Hof. destruct (r5_of_reg rd) as [d|] eqn:Hrd; [|discriminate]. destruct (r5_of_reg rs1) as [s|] eqn:Hrs1; [|discriminate].
    destruct (r5_of_reg rs2) as [s2|] eqn:Hrs2; [|discriminate].
    injection Hof as <-. cbn [exec] in Hx.
    destruct (aligned (s_facts st) (getr st s) (awidth_log w)) eqn:AL; [|discriminate].
    pose proof (amo_aligned_ok E (s_facts st) (getr st s) w (so_facts _ _ _ _ _ _ HS) AL) as AA.
    rewrite <- (getr_den segs OPS E st ms model s rs1 HS Hrs1) in AA.
    pose proof (so_resv _ _ _ _ _ _ HS) as RV.
    cbn [Sem.exec] in HI. rewrite AA in HI. cbn [negb] in HI. cbn [c_resv core_of] in HI.
    destruct (s_resv st) as [|a'|] eqn:SR; cbn [resv_ok] in RV; [| |discriminate].
    + rewrite RV in HI. rewrite (interp_acc_EDone _ _ _ HI). constructor.
    + rewrite RV in HI.
      destruct (decide_eq (s_facts st) a' (getr st s)) as [[|]|] eqn:D; [| |discriminate].
      * destruct (do_store segs (setresv st RNone) (getr st s) (awidth_bytes w) (getr st s2)) as [st1|why] eqn:DS; [|discriminate].
        eapply Forall_impl; [|exact FA]. intros [a n] [X1 X2]. cbn [fst snd] in *. subst a n.
        rewrite (getr_den segs OPS E st ms model s rs1 HS Hrs1).
        pose proof (do_store_acc0 E (setresv st RNone) (ms_mem ms) _ _ _ st1 (so_zero _ _ _ _ _ _ HS) (so_facts _ _ _ _ _ _ HS)
                      (so_reg _ _ _ _ _ _ HS) (awidth_wok w) DS) as ACC.
        replace (Z.of_nat (Acc.aw_nat w)) with (to_Z (awidth_bytes w)) by (destruct w; reflexivity). exact ACC.
      * apply (decide_eq_sound E _ (so_facts _ _ _ _ _ _ HS)) in D. apply (proj1 (eqb_iff _ _ false)) in D.
        destruct (Z.eqb_spec (bv_unsigned (den E a')) (bv_unsigned (rget (core_of ms) rs1))) as [X|X].
        { exfalso. apply D. apply bv_eq. rewrite X. rewrite (getr_den segs OPS E st ms model s rs1 HS Hrs1). reflexivity. }
        rewrite (interp_acc_EDone _ _ _ HI). constructor.
  -
    unfold of_instr in Hof. destruct (r5_of_reg rd) as [d|] eqn:Hrd; [|discriminate]. destruct (r5_of_reg rs1) as [s|] eqn:Hrs1; [|discriminate].
    destruct (r5_of_reg rs2) as [s2|] eqn:Hrs2; [|discriminate].
    injection Hof as <-. cbn [exec] in Hx.
    destruct (aligned (s_facts st) (getr st s) (awidth_log w)) eqn:AL; [|discriminate].
    destruct (do_load segs st (getr st s) (awidth_bytes w) true) as [[v|]|why] eqn:DL; try discriminate.
    eapply Forall_impl; [|exact FA]. intros [a n] [X1 X2]. cbn [fst snd] in *. subst a n.
    rewrite (getr_den segs OPS E st ms model s rs1 HS Hrs1).
    pose proof (do_load_acc E st ms model _ _ _ v HS (awidth_wok w) DL) as ACC.
    replace (Z.of_nat (Acc.aw_nat w)) with (to_Z (awidth_bytes w)) by (destruct w; reflexivity). exact ACC.
  -
    unfold of_instr in Hof. destruct (r5_of_reg rd) as [d|] eqn:Hrd; [|discriminate]. destruct (r5_of_reg rs1) as [s|] eqn:Hrs1; [|discriminate].
    injection Hof as <-. cbn [exec] in Hx.
    eapply Forall_impl; [|exact FA]. intros [a n] [X1 X2]. cbn [fst snd] in *. subst a n.
    rewrite (ea_den segs OPS E st ms model s rs1 _ imm HS Hrs1).
    destruct fmt.
    + destruct (do_load segs st (sv_alu ALU_ADD (getr st s) (VL (w_of_imm imm))) 4%uint63 false) as [[v|]|why] eqn:DL; try discriminate.
      exact (do_load_acc E st ms model _ _ _ v HS wok4 DL).
    + destruct (do_load segs st (sv_alu ALU_ADD (getr st s) (VL (w_of_imm imm))) 8%uint63 false) as [[v|]|why] eqn:DL; try discriminate.
      exact (do_load_acc E st ms model _ _ _ v HS wok8 DL).
  -
    unfold of_instr in Hof. destruct (r5_of_reg rs1) as [s|] eqn:Hrs1; [|discriminate]. destruct (r5_of_reg rs2) as [s2|] eqn:Hrs2; [|discriminate].
    injection Hof as <-. cbn [exec] in Hx.
    eapply Forall_impl; [|exact FA]. intros [a n] [X1 X2]. cbn [fst snd] in *. subst a n.
    rewrite (ea_den segs OPS E st ms model s rs1 _ imm HS Hrs1).
    destruct fmt; cbv zeta in Hx.
    + destruct (do_store segs st (sv_alu ALU_ADD (getr st s) (VL (w_of_imm imm))) 4%uint63 (getf st s2)) as [st1|why] eqn:DS; [|discriminate].
      exact (do_store_acc E st ms model _ _ _ st1 HS wok4 DS).
    + destruct (do_store segs st (sv_alu ALU_ADD (getr st s) (VL (w_of_imm imm))) 8%uint63 (getf st s2)) as [st1|why] eqn:DS; [|discriminate].
      exact (do_store_acc E st ms model _ _ _ st1 HS wok8 DS).
Qed.

Lemma s_ops_setr : forall st r v, s_ops (setr st r v) = s_ops st.
Proof. intros st r v. destruct r; reflexivity. Qed.

Lemma do_store_ops : forall st a w v st', do_store segs st a w v = inl st' -> s_ops st' = s_ops st.
Proof.
  intros st a w v st' H. destruct (do_store_inv segs st a w v st' H) as (k & o & r & key & _ & _ & _ & _ & ->). reflexivity.
Qed.

Lemma exec_ops : forall fi st st', exec segs fi st = XOk st' -> s_ops st' = s_ops st.
Proof.
  intros fi st st' H. destruct fi; cbn [exec] in H;
  repeat match type of H with
  | XStop _ = XOk _ => discriminate H
  | XOk _ = XOk _ => injection H as <-
  | (match ?x with _ => _ end) = XOk _ => destruct x eqn:?
  end;
  cbn [s_ops setpc setf setresv addfact]; rewrite ?s_ops_setr; cbn [s_ops setresv];
  try reflexivity;
  repeat match goal with
  | Hd : do_store _ _ _ _ _ = inl ?s |- _ => apply do_store_ops in Hd; rewrite ?Hd; clear Hd
  end; cbn [s_ops setresv]; rewrite ?s_ops_setr; try reflexivity.
  all: fail "exec_ops: unsolved".
Qed.

End WithSegs.
End StepAcc.
