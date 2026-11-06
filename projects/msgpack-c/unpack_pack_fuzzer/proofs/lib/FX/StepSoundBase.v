(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step ValProofs.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step ValP.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module StepB.

Definition core_of (ms : machine_state) : core :=
  Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms).

Definition ms_upd (ms : machine_state) (c : core) (m' : word -> option byte) : machine_state :=
  {| ms_regs := c_regs c; ms_fregs := c_fregs c; ms_pc_val := c_pc c;
     ms_svc_pending := None; ms_resv := c_resv c; ms_fcsr := c_fcsr c;
     ms_mem := m'; ms_rom := ms_rom ms |}.

Section WithSegs.
Variable segs : list Segment.
Variable OPS : optable.

Ltac cbn_st := cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next setpc setf setresv setregs addfact
                    ms_upd c_regs c_fregs c_pc c_fcsr c_resv
                    ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending
                    with_pc with_regs with_fregs with_resv with_fcsr core_of rget fget rset fset].

Lemma step_exec : forall ms w i,
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  RiscvSemantics.step segs ms =
    match interp_eff segs (Sem.exec (Z_to_bv 64 4) i (core_of ms)) (ms_mem ms) with
    | MachineOk (c, m') => MachineOk (ms_upd ms c m')
    | MachineFault => MachineFault
    | MachineUnmodeled => MachineUnmodeled
    end.
Proof.
  intros ms w i Hf He Hd.
  unfold RiscvSemantics.step, step_accesses. unfold ms_pc. rewrite Hf.
  unfold drop_access_report, decode_exec_accesses. rewrite He, Hd.
  unfold interp_eff, drop_access_report, core_of.
  destruct (interp_eff_accesses segs _ (ms_mem ms)) as [[[c m'] acc]| |]; reflexivity.
Qed.

Lemma itab_find : forall it pc fi, itab_ok segs it -> IMap.find pc it = Some fi ->
  exists w, fetch_word segs (Z_to_bv 64 (to_Z pc)) = Some w /\
    ((is_ecall w = true /\ fi = IEcall) \/
     (is_ecall w = false /\ exists i, decode_any w = Some (i, 4%Z) /\ of_instr i = Some fi)).
Proof.
  intros it pc fi Hok Hf. specialize (Hok pc fi Hf). unfold decode_at in Hok.
  destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w|]; [|discriminate].
  exists w. split; [reflexivity|].
  destruct (is_ecall w) eqn:He.
  - left. split; [reflexivity|congruence].
  - right. split; [reflexivity|].
    destruct (decode_any w) as [[i isz]|]; [|discriminate].
    destruct isz as [|p|p]; try discriminate.
    destruct p as [p|p|]; try discriminate. destruct p as [p|p|]; try discriminate. destruct p; try discriminate.
    exists i. split; [reflexivity|exact Hok].
Qed.

Lemma is_x0_reg_of_r5 : forall rd, is_x0 (reg_of_r5 rd) = r5_eqb rd X0.
Proof. intros rd; destruct rd; reflexivity. Qed.

Lemma r5_of_Z_sound : forall z d, r5_of_Z z = Some d -> z = r5_to_Z d.
Proof.
  intros z d H. destruct z as [|p|p]; [inversion H; reflexivity| |discriminate].
  do 6 (try (destruct p as [p|p|])); cbn in H; try discriminate; inversion H; reflexivity.
Qed.
Lemma reg_of_r5_of_reg : forall r d, r5_of_reg r = Some d -> reg_of_r5 d = r.
Proof.
  intros r d H. unfold r5_of_reg in H. apply r5_of_Z_sound in H.
  unfold reg_of_r5. rewrite <- H. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma reg_get_set : forall (regs : bvmap 5 word) (rd r : r5) wv,
  reg_get (bvmap_set (reg_of_r5 rd) wv regs) (reg_of_r5 r) = if r5_eqb r rd then wv else reg_get regs (reg_of_r5 r).
Proof.
  intros. unfold reg_get.
  destruct (r5_eqb r rd) eqn:Heq.
  - apply r5_eqb_spec in Heq. subst. rewrite bvmap_get_set_same. reflexivity.
  - rewrite bvmap_get_set_other; [reflexivity|].
    intro HH. assert (r = rd).
    { apply (f_equal bv_unsigned) in HH. unfold reg_of_r5 in HH. rewrite !Z_to_bv_unsigned in HH.
      destruct rd, r; cbn in HH; try reflexivity; discriminate. }
    subst. rewrite (proj2 (r5_eqb_spec rd rd) eq_refl) in Heq. discriminate.
Qed.

Lemma r5_eqb_refl : forall r, r5_eqb r r = true.
Proof. intros r. apply (proj2 (r5_eqb_spec r r) eq_refl). Qed.

Lemma setr_eq : forall st rd v, r5_eqb rd X0 = false ->
  setr st rd v = SS (s_pc st) (rf_set (s_rf st) rd v) (s_ff st) (s_resv st) (s_regs st) (s_facts st) (s_ops st) (s_priv st) (s_next st).
Proof. intros st rd v H. unfold setr. destruct rd; try reflexivity. cbn in H. discriminate. Qed.
Lemma setr_x0 : forall st v, setr st X0 v = st.
Proof. reflexivity. Qed.

Lemma st_ok_reg_pc : forall E st ms model rd (v : sv) (wv : word) (npci : int),
  st_ok segs OPS E st ms model ->
  den E v = wv ->
  st_ok segs OPS E (setpc (setr st rd v) npci)
        (ms_upd ms (rset (reg_of_r5 rd) wv (with_pc (Z_to_bv 64 (to_Z npci)) (core_of ms))) (ms_mem ms)) model.
Proof.
  intros E st ms model rd v wv npci HS Hv.
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf].
  unfold rset. rewrite is_x0_reg_of_r5.
  destruct (r5_eqb rd X0) eqn:Hx.
  - apply r5_eqb_spec in Hx. subst rd. split; cbn_st; try assumption; try reflexivity.
  - rewrite (setr_eq st rd v Hx).
    split; cbn_st; try assumption; try reflexivity.
    + rewrite rf_get_set_other; [assumption|]. intro; subst; discriminate.
    + intros r. unfold rget; cbn [c_regs]. rewrite is_x0_reg_of_r5. rewrite reg_get_set.
      destruct (r5_eqb r X0) eqn:H0.
      * apply r5_eqb_spec in H0; subst r. rewrite rf_get_set_other; [|intro; subst; discriminate].
        rewrite Hx0. reflexivity.
      * destruct (r5_eqb r rd) eqn:H1.
        -- apply r5_eqb_spec in H1; subst r. rewrite rf_get_set_same. symmetry; exact Hv.
        -- rewrite rf_get_set_other. 2:{ intro HH; subst r. rewrite r5_eqb_refl in H1. discriminate. }
           specialize (Hregs r). unfold rget in Hregs. cbn [c_regs] in Hregs. rewrite is_x0_reg_of_r5, H0 in Hregs. exact Hregs.
Qed.

Lemma st_ok_freg_pc : forall E st ms model rd (v : sv) (wv : word) (npci : int),
  st_ok segs OPS E st ms model ->
  den E v = wv ->
  st_ok segs OPS E (setpc (setf st rd v) npci)
        (ms_upd ms (fset (reg_of_r5 rd) wv (with_pc (Z_to_bv 64 (to_Z npci)) (core_of ms))) (ms_mem ms)) model.
Proof.
  intros E st ms model rd v wv npci HS Hv.
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf].
  split; cbn_st; try assumption; try reflexivity.
  - intros r. rewrite reg_get_set. destruct (r5_eqb r rd) eqn:H1.
    + apply r5_eqb_spec in H1; subst r. rewrite rf_get_set_same. symmetry; exact Hv.
    + rewrite rf_get_set_other. 2:{ intro HH; subst r. rewrite r5_eqb_refl in H1. discriminate. }
      exact (Hfregs r).
Qed.

Lemma st_ok_pc : forall E st ms model (npci : int),
  st_ok segs OPS E st ms model ->
  st_ok segs OPS E (setpc st npci)
        (ms_upd ms (with_pc (Z_to_bv 64 (to_Z npci)) (core_of ms)) (ms_mem ms)) model.
Proof.
  intros E st ms model npci HS.
  destruct HS as [Hpc Hx0 Hregs Hfregs Hsvc Hresv Hfcsr Hrom Hz Hbst Hreg Hdisj Hpub Hfacts Hops Hapart Hmf].
  split; cbn_st; try assumption; try reflexivity.
Qed.

Lemma pc4_ok : forall pc, PrimInt63.ltb pc bit62i = true ->
  Z_to_bv 64 (to_Z (PrimInt63.add pc 4%uint63)) = (Z_to_bv 64 (to_Z pc) + Z_to_bv 64 4)%bv.
Proof.
  intros pc H. apply Uint63.ltb_spec in H. change (to_Z bit62i) with (2^62) in H.
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned.
  rewrite Uint63.add_spec. change (to_Z 4%uint63) with 4.
  unfold bv_wrap, bv_modulus. change wB with (2^63).
  rewrite (Z.mod_small (to_Z pc + 4)) by (pose proof (Uint63.to_Z_bounded pc); lia).
  rewrite (Z.mod_small (to_Z pc)) by (pose proof (Uint63.to_Z_bounded pc); change wB with (2^63) in *; lia).
  reflexivity.
Qed.

Lemma pc_add_ok : forall pc off t, pc_add pc off = Some t ->
  Z_to_bv 64 (to_Z t) = (Z_to_bv 64 (to_Z pc) + wbv off)%bv.
Proof.
  intros pc off t H. unfold pc_add in H.
  remember (wadd (wlit pc) off) as s eqn:Hs.
  destruct (wt s) eqn:Ht; cbn [negb andb] in H; [discriminate|].
  destruct (PrimInt63.ltb (wl s) bit62i) eqn:Hl; [|discriminate].
  injection H as Htt. subst t.
  pose proof (wadd_ok (wlit pc) off) as Ha. rewrite <- Hs in Ha.
  assert (Hw : w2Z s = to_Z (wl s)).
  { unfold w2Z. rewrite Ht. lia. }
  apply bv_eq. rewrite bv_add_unsigned. rewrite !Z_to_bv_unsigned. rewrite <- Hw, Ha, wlit_ok, <- wbv_unsigned.
  unfold wbv. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change two64 with (2^64).
  change (2 ^ Z.of_N 64) with (2^64).
  rewrite (Z.mod_small (to_Z pc)) by (pose proof (Uint63.to_Z_bounded pc); change wB with (2^63) in *; lia).
  rewrite Zmod_mod. reflexivity.
Qed.

Definition case_stmt (i : instr) (fi : finstr) : Prop :=
  forall E st ms model st',
    st_ok segs OPS E st ms model ->
    PrimInt63.ltb (s_pc st) bit62i = true ->
    of_instr i = Some fi ->
    exec segs fi st = XOk st' ->
    exists c m', interp_eff segs (Sem.exec (Z_to_bv 64 4) i (core_of ms)) (ms_mem ms) = MachineOk (c, m')
                 /\ st_ok segs OPS E st' (ms_upd ms c m') model.

End WithSegs.
End StepB.
