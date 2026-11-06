(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
Module LStep.
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition boff (a : word) (k : nat) : word := (a + Z_to_bv 64 (Z.of_nat k))%bv.

Lemma boff_0 : forall a, boff a 0 = a.
Proof.
  intros a. unfold boff. apply bv_eq. rewrite bv_add_unsigned, Z_to_bv_unsigned.
  change (bv_wrap 64 (Z.of_nat 0)) with 0%Z.
  rewrite Z.add_0_r. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma boff_S : forall a k, boff a (S k) = boff (a + 1)%bv k.
Proof.
  intros a k. unfold boff. apply bv_eq.
  rewrite !bv_add_unsigned, !Z_to_bv_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z.
  unfold bv_wrap. rewrite Nat2Z.inj_succ.
  rewrite Zplus_mod_idemp_r, Zplus_mod_idemp_r, Zplus_mod_idemp_l.
  f_equal. lia.
Qed.

Lemma bv_eqb_true : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Section WithSegs.
Variable segs : list Segment.
Variable zf : word -> bool.
Variable X : word -> Prop.
Hypothesis HL : zf_noseg segs zf.
Hypothesis HWX : no_wx segs.
Local Notation magree := (LBase.magree segs zf X).

(* [comment removed for export] *)
Definition vis (mv : mem) (x : word) : Prop := mv x <> None \/ ~ noseg segs x.

Lemma vis_mono : forall mv mv' x, (forall y, mv y <> None -> mv' y <> None) -> vis mv x -> vis mv' x.
Proof. intros mv mv' x H [Hv|Hs]; [left; apply H; exact Hv| right; exact Hs]. Qed.

(* [comment removed for export] *)

Lemma lmem_at_seg : forall mv x, ~ noseg segs x -> lmem zf mv x = mv x.
Proof.
  intros mv x Hs. unfold lmem. destruct (mv x); [reflexivity|].
  destruct (zf x) eqn:E; [|reflexivity]. exfalso. apply Hs. exact (proj1 (HL _ E)).
Qed.

Lemma find_segment_some_not_noseg : forall x n s,
  0 < n -> find_segment segs (bv_unsigned x) n = Some s -> ~ noseg segs x.
Proof.
  intros x n s Hn H Hns. induction segs as [|s0 r IH] in H, Hns; [discriminate|].
  cbn in H. destruct (Z.leb_spec0 (Z.of_N (seg_base s0)) (bv_unsigned x));
  destruct (Z.leb_spec0 (bv_unsigned x + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0))); cbn in H.
  - apply (Hns s0 (or_introl eq_refl)). lia.
  - apply IH; [exact H|]. intros s' Hs'. apply Hns. right; exact Hs'.
  - apply IH; [exact H|]. intros s' Hs'. apply Hns. right; exact Hs'.
  - apply IH; [exact H|]. intros s' Hs'. apply Hns. right; exact Hs'.
Qed.

(* [comment removed for export] *)

Lemma ov_read_bytes_ext : forall n mv mr a bs,
  magree mv mr ->
  ov_read_bytes segs mv a n = Some bs ->
  ov_read_bytes segs mr a n = Some bs /\ (forall k, (k < n)%nat -> vis mv (boff a k)).
Proof.
  induction n as [|n IH]; intros mv mr a bs Hm H.
  - cbn in H |- *. split; [exact H|]. intros k Hk. lia.
  - cbn [ov_read_bytes] in H |- *.
    destruct (mv a) as [b|] eqn:Ea.
    + rewrite (magree_some segs zf X mv mr a b Hm Ea).
      destruct (ov_read_bytes segs mv (a + 1) n) as [rest|] eqn:Er; [|discriminate].
      destruct (IH mv mr (a + 1)%bv rest Hm Er) as [-> Hvis].
      split; [exact H|]. intros k Hk. destruct k as [|k].
      * rewrite boff_0. left. congruence.
      * rewrite boff_S. apply Hvis. lia.
    + destruct (memory_read segs a 1) as [[|b l]|] eqn:Emr; [discriminate| |discriminate].
      assert (Hs : ~ noseg segs a).
      { intros Hns. rewrite (memory_read_noseg segs a 1 Hns ltac:(lia)) in Emr. discriminate. }
      assert (El : zf a = false).
      { destruct (zf a) eqn:E; [|reflexivity]. exfalso. apply Hs. exact (proj1 (HL _ E)). }
      rewrite (magree_seg segs zf X mv mr a Hm Hs). unfold lmem at 1. rewrite Ea, El.
      destruct (ov_read_bytes segs mv (a + 1) n) as [rest|] eqn:Er; [|discriminate].
      destruct (IH mv mr (a + 1)%bv rest Hm Er) as [-> Hvis].
      split; [exact H|]. intros k Hk. destruct k as [|k].
      * rewrite boff_0. right. exact Hs.
      * rewrite boff_S. apply Hvis. lia.
Qed.

(* [comment removed for export] *)

Lemma wview_ext : forall mv mr x, magree mv mr ->
  wview segs mv x <> None -> wview segs mr x <> None /\ vis mv x.
Proof.
  intros mv mr x Hm H. unfold wview in H |- *.
  destruct (mv x) as [b|] eqn:Ex.
  - rewrite (magree_some segs zf X mv mr x b Hm Ex). split; [discriminate| left; congruence].
  - destruct (find_segment segs (bv_unsigned x) 1) as [s|] eqn:Ef; [|congruence].
    assert (Hs : ~ noseg segs x) by (eapply find_segment_some_not_noseg; [| exact Ef]; lia).
    assert (El : zf x = false).
    { destruct (zf x) eqn:E; [|reflexivity]. exfalso. apply Hs. exact (proj1 (HL _ E)). }
    rewrite (magree_seg segs zf X mv mr x Hm Hs). unfold lmem. rewrite Ex, El. split; [exact H| right; exact Hs].
Qed.

Lemma store_ok_ext : forall n mv mr a,
  magree mv mr ->
  store_ok segs mv a n = true ->
  store_ok segs mr a n = true /\ (forall k, (k < n)%nat -> vis mv (boff a k)).
Proof.
  induction n as [|n IH]; intros mv mr a Hm H.
  - split; [reflexivity|]. intros k Hk. lia.
  - cbn [store_ok] in H |- *.
    destruct (wview segs mv a) as [b|] eqn:Ew; [|discriminate].
    destruct (wview_ext mv mr a Hm ltac:(congruence)) as [Hw Hv].
    destruct (wview segs mr a); [|congruence].
    destruct (IH mv mr (a + 1)%bv Hm H) as [-> Hvis].
    split; [reflexivity|]. intros k Hk. destruct k as [|k].
    + rewrite boff_0. exact Hv.
    + rewrite boff_S. apply Hvis. lia.
Qed.

Lemma write_to_mem_mono : forall bs m a x, m x <> None -> write_to_mem m a bs x <> None.
Proof.
  induction bs as [|b bs IH]; intros m a x H; cbn; [exact H|].
  apply IH. destruct (bv_eqb x a); [discriminate| exact H].
Qed.

Lemma write_to_mem_new : forall bs m a x, write_to_mem m a bs x <> None -> m x = None ->
  exists k, (k < length bs)%nat /\ x = boff a k.
Proof.
  induction bs as [|b bs IH]; intros m a x H Hx; cbn in H.
  - congruence.
  - destruct (bv_eqb x a) eqn:E.
    + exists 0%nat. split; [cbn; lia|]. rewrite boff_0. apply bv_eqb_true in E. exact E.
    + destruct (IH _ _ _ H) as (k & Hk & ->).
      * cbn beta. rewrite E. exact Hx.
      * exists (S k). split; [cbn; lia|]. rewrite boff_S. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma magree_write_to_mem : forall bs mv mr a,
  magree mv mr -> magree (write_to_mem mv a bs) (write_to_mem mr a bs).
Proof.
  induction bs as [|b bs IH]; intros mv mr a Hm; cbn [write_to_mem]; [exact Hm|].
  apply IH. intros x. unfold lmem. destruct (bv_eqb x a) eqn:E; [left; reflexivity|].
  destruct (Hm x) as [H | H]; [left| right]; [| exact H]. unfold lmem in H. exact H.
Qed.

(* [comment removed for export] *)

Lemma interp_ext : forall t mv mr c mv',
  magree mv mr ->
  interp_eff0 segs t mv = MachineOk (c, mv') ->
  exists mr' acc,
    interp_eff_accesses segs t mr = MachineOk (@mkAccessReport _ (c, mr') acc)
    /\ magree mv' mr'
    /\ (forall x, mv x <> None -> mv' x <> None)
    /\ (forall x, mv' x <> None -> vis mv x)
    /\ (forall a n, In (a, n) acc -> forall k, (k < n)%nat -> vis mv' (boff a k)).
Proof.
  induction t as [c0 | c0 | c0 | c0 | c0 | c0 | n a k IH | n a v k IH];   (* [comment removed for export] *)
    intros mv mr c mv' Hm H; cbn [interp_eff0 interp_eff_accesses] in H |- *; try discriminate.
  - injection H as <- <-. exists mr, []. split; [reflexivity|]. split; [exact Hm|].
    split; [auto|]. split; [intros x Hx; left; exact Hx|]. intros a' n' [].
  - destruct (ov_read_bytes segs mv a (width_bytes n)) as [bs|] eqn:Er; [|discriminate].
    destruct (ov_read_bytes_ext _ _ _ _ _ Hm Er) as [-> Hvis].
    destruct (IH _ _ _ _ _ Hm H) as (mr' & acc & Hk & Hm' & Hmono & Hnew & Hacc).
    rewrite Hk. exists mr', ((a, width_bytes n) :: acc). split; [reflexivity|].
    split; [exact Hm'|]. split; [exact Hmono|]. split; [exact Hnew|].
    intros a' n' [Hin|Hin]; [| exact (Hacc a' n' Hin)].
    injection Hin as <- <-. intros j Hj. eapply vis_mono; [exact Hmono|]. apply Hvis. exact Hj.
  - destruct (store_ok segs mv a (width_bytes n)) eqn:Es; [|discriminate].
    destruct (store_ok_ext _ _ _ _ Hm Es) as [Hs' Hvis]. rewrite Hs'.
    set (bs := Z_to_le_bytes (width_bytes n) (bv_unsigned v)) in *.
    pose proof (magree_write_to_mem bs mv mr a Hm) as Hm1.
    destruct (IH _ _ _ _ Hm1 H) as (mr' & acc & Hk & Hm' & Hmono & Hnew & Hacc).
    rewrite Hk. exists mr', ((a, width_bytes n) :: acc). split; [reflexivity|].
    split; [exact Hm'|].
    assert (Hlen : length bs = width_bytes n) by (unfold bs; apply length_Z_to_le_bytes).
    split; [intros x Hx; apply Hmono; apply write_to_mem_mono; exact Hx|].
    split.
    + intros x Hx. destruct (Hnew x Hx) as [Hw|Hsg]; [| right; exact Hsg].
      destruct (mv x) eqn:Ex; [left; congruence|].
      destruct (write_to_mem_new _ _ _ _ Hw Ex) as (j & Hj & ->). apply Hvis. lia.
    + intros a' n' [Hin|Hin]; [| exact (Hacc a' n' Hin)].
      injection Hin as <- <-. intros j Hj. eapply vis_mono; [exact Hmono|].
      eapply vis_mono; [intros y; apply write_to_mem_mono|]. apply Hvis. exact Hj.
Qed.


(* [comment removed for export] *)

Lemma find_segment_In : forall ss z n s, find_segment ss z n = Some s -> In s ss.
Proof.
  induction ss as [|s0 r IH]; intros z n s H; cbn in H; [discriminate|].
  destruct (Z.leb (Z.of_N (seg_base s0)) z && Z.leb (z + n) (Z.of_N (seg_base s0) + Z.of_N (seg_size s0)))%bool.
  - injection H as ->. left; reflexivity.
  - right. eapply IH. exact H.
Qed.

Lemma code_read_ov_none : forall m a n, code_read_ov segs m a n = None.
Proof.
  intros m a n. unfold code_read_ov.
  destruct (find_segment segs (bv_unsigned a) (Z.of_N n)) as [s|] eqn:E; [|reflexivity].
  rewrite (proj1 HWX s (find_segment_In _ _ _ _ E)). reflexivity.
Qed.

Lemma fetch_word_ov_none : forall m a, fetch_word_ov segs m a = None.
Proof.
  intros m a. unfold fetch_word_ov. rewrite code_read_ov_none.
  destruct (negb (bv_unsigned a mod 2 =? 0)); reflexivity.
Qed.

Lemma fetch_half_any_indep : forall m m' a, fetch_half_any segs m a = fetch_half_any segs m' a.
Proof.
  intros m m' a. unfold fetch_half_any, fetch_half_ov. rewrite !code_read_ov_none. reflexivity.
Qed.

Lemma fetch_tail_any_indep : forall m m' a, fetch_tail_any segs m a = fetch_tail_any segs m' a.
Proof.
  intros m m' a. unfold fetch_tail_any.
  rewrite (fetch_half_any_indep m m' a), (fetch_half_any_indep m m' (a + 2)%bv). reflexivity.
Qed.

Lemma fetch_failure_indep : forall m m' a, fetch_failure segs m a = fetch_failure segs m' a.
Proof.
  intros m m' a. unfold fetch_failure. rewrite (fetch_half_any_indep m m' a). reflexivity.
Qed.

Lemma fetch_failure_not_ok : forall m a st, fetch_failure segs m a <> MachineOk st.
Proof.
  intros m a st. unfold fetch_failure.
  destruct (negb (bv_unsigned a mod 2 =? 0)); [discriminate|].
  match goal with |- (if ?b then _ else _) <> _ => destruct b; discriminate end.
Qed.

(* [comment removed for export] *)
Definition msw (ms : machine_state) (m : mem) : machine_state :=
  {| ms_regs := ms_regs ms; ms_fregs := ms_fregs ms; ms_pc_val := ms_pc_val ms;
     ms_svc_pending := ms_svc_pending ms; ms_resv := ms_resv ms; ms_fcsr := ms_fcsr ms;
     ms_mem := m; ms_rom := ms_rom ms |}.

Lemma msw_MS : forall R F pc fc rv m ro m', msw (MS R F pc fc rv m ro) m' = MS R F pc fc rv m' ro.
Proof. reflexivity. Qed.

Lemma msw_self : forall ms, msw ms (ms_mem ms) = ms.
Proof. intros []; reflexivity. Qed.

Lemma msw_msw : forall ms m m', msw (msw ms m) m' = msw ms m'.
Proof. reflexivity. Qed.

Lemma ms_mem_msw : forall ms m, ms_mem (msw ms m) = m. Proof. reflexivity. Qed.
Lemma ms_svc_pending_msw : forall ms m, ms_svc_pending (msw ms m) = ms_svc_pending ms. Proof. reflexivity. Qed.
Lemma ms_pc_msw : forall ms m, ms_pc (msw ms m) = ms_pc ms. Proof. reflexivity. Qed.

(* [comment removed for export] *)

Definition ext_post (mv mv' : mem) (acc : list memory_access) : Prop :=
  (forall x, mv x <> None -> mv' x <> None)
  /\ (forall x, mv' x <> None -> vis mv x)
  /\ (forall a n, In (a, n) acc -> forall k, (k < n)%nat -> vis mv' (boff a k)).

Lemma decode_exec_accesses_ext : forall ms mr w ms1,
  magree (ms_mem ms) mr ->
  decode_exec segs ms w = MachineOk ms1 ->
  exists mr' acc,
    decode_exec_accesses segs (msw ms mr) w = MachineOk (@mkAccessReport _ (msw ms1 mr') acc)
    /\ magree (ms_mem ms1) mr'
    /\ ext_post (ms_mem ms) (ms_mem ms1) acc.
Proof.
  intros ms mr w ms1 Hm H.
  unfold decode_exec, RiscvSemantics.drop_access_report in H. unfold decode_exec_accesses in H |- *.
  destruct (is_ecall w).
  - injection H as <-. exists mr, []. split; [destruct ms; reflexivity|].
    split; [exact Hm|]. split; [auto|]. split; [intros x Hx; left; exact Hx| intros a n []].
  - destruct (decode_any w) as [[i isz]|]; [| destruct (is_defined_illegal w); discriminate].
    cbn [ms_regs ms_fregs ms_pc_val ms_fcsr ms_resv ms_mem ms_rom msw].
    destruct (interp_eff_accesses segs (exec (Z_to_bv 64 isz) i _) (ms_mem ms)) as [[[c m1] acc0]| |] eqn:E;
      [| discriminate | discriminate].
    cbn in H. injection H as <-.
    assert (E0 : interp_eff0 segs (exec (Z_to_bv 64 isz) i
              {| c_regs := ms_regs ms; c_fregs := ms_fregs ms; c_pc := ms_pc_val ms;
                 c_fcsr := ms_fcsr ms; c_resv := ms_resv ms |}) (ms_mem ms) = MachineOk (c, m1)).
    { rewrite <- interp_eff0_ok. unfold interp_eff, RiscvSemantics.drop_access_report. rewrite E. reflexivity. }
    destruct (interp_ext _ _ _ _ _ Hm E0) as (mr' & acc & Hk & Hm' & Hmono & Hnew & Hacc).
    rewrite Hk. cbn. exists mr', acc. split; [reflexivity|]. split; [exact Hm'|].
    split; [exact Hmono|]. split; [exact Hnew| exact Hacc].
Qed.

Lemma step_accesses_ext : forall ms mr ms1,
  magree (ms_mem ms) mr ->
  RiscvSemantics.step segs ms = MachineOk ms1 ->
  exists mr' acc,
    RiscvSemantics.step_accesses segs (msw ms mr) = MachineOk (@mkAccessReport _ (msw ms1 mr') acc)
    /\ magree (ms_mem ms1) mr'
    /\ ext_post (ms_mem ms) (ms_mem ms1) acc.
Proof.
  intros ms mr ms1 Hm H.
  unfold RiscvSemantics.step, RiscvSemantics.drop_access_report in H.
  unfold RiscvSemantics.step_accesses in H |- *. rewrite ms_pc_msw. cbn [ms_mem msw].
  destruct (fetch_word segs (ms_pc ms)) as [w|] eqn:Ef.
  - apply (decode_exec_accesses_ext ms mr w ms1 Hm).
    unfold decode_exec, RiscvSemantics.drop_access_report. exact H.
  - rewrite fetch_word_ov_none in H |- *.
    rewrite (fetch_tail_any_indep mr (ms_mem ms)).
    destruct (fetch_tail_any segs (ms_mem ms) (ms_pc ms)) as [w|] eqn:Et.
    + apply (decode_exec_accesses_ext ms mr w ms1 Hm).
      unfold decode_exec, RiscvSemantics.drop_access_report. exact H.
    + exfalso. destruct (fetch_failure segs (ms_mem ms) (ms_pc ms)) eqn:Eff; try discriminate.
      exact (fetch_failure_not_ok _ _ _ Eff).
Qed.


End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pb_wrap : forall w, 0 <= w -> (w / 4096 * 4096) mod 2^64 = ((w mod 2^64) / 4096 * 4096) mod 2^64.
Proof.
  intros w Hw. rewrite (Z.div_mod w (2^64)) at 1 by lia.
  replace (2^64 * (w / 2^64) + w mod 2^64) with ((w / 2^64 * 2^52) * 4096 + w mod 2^64) by lia.
  rewrite Z.div_add_l by lia.
  rewrite Z.mul_add_distr_r.
  replace (w / 2 ^ 64 * 2 ^ 52 * 4096) with ((w / 2^64) * 2^64) by lia.
  rewrite Z.add_comm, Z_mod_plus_full. reflexivity.
Qed.

Lemma page_base_of_boff : forall (a : word) (k : nat),
  page_base_of (bv_unsigned a + Z.of_nat k) = page_base (boff a k).
Proof.
  intros a k. unfold page_base, boff, page_base_of. rewrite page_size_eq.
  rewrite bv_add_unsigned, Z_to_bv_unsigned. apply bv_eq. rewrite !Z_to_bv_unsigned.
  pose proof (bv_unsigned_in_range 64 a) as Ha. change (bv_modulus 64) with (2^64) in Ha.
  unfold bv_wrap. change (bv_modulus 64) with (2^64).
  rewrite Zplus_mod_idemp_r. apply pb_wrap. lia.
Qed.

Lemma page_insert_in : forall p q pages,
  In p (page_insert q pages) -> p = q \/ In p pages.
Proof.
  intros p q pages H. unfold page_insert in H.
  destruct (page_mem q pages); [right; exact H|].
  destruct H as [Hqp | H]; [left; symmetry; exact Hqp | right; exact H].
Qed.

Lemma page_mem_In : forall p pages, page_mem p pages = true <-> In p pages.
Proof.
  intros p pages. unfold page_mem. rewrite existsb_exists. split.
  - intros (q & Hin & He). apply bv_eqb_true in He. subst; exact Hin.
  - intros Hin. exists p. split; [exact Hin| apply bv_eqb_refl].
Qed.

Lemma NoDup_page_insert : forall q pages, List.NoDup pages -> List.NoDup (page_insert q pages).
Proof.
  intros q pages H. unfold page_insert. destruct (page_mem q pages) eqn:E; [exact H|].
  constructor; [|exact H]. intros Hin. apply page_mem_In in Hin. congruence.
Qed.

Lemma access_pages_acc_in : forall n base pages p,
  In p (access_pages_acc base n pages) ->
  In p pages \/ exists k, (k < n)%nat /\ p = page_base_of (base + Z.of_nat k).
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages p H.
  - left; exact H.
  - destruct (IH (base + 1)%Z _ p H) as [Hin | (k & Hk & ->)].
    + destruct (page_insert_in _ _ _ Hin) as [-> | Hin'].
      * right. exists 0%nat. split; [lia|]. f_equal. lia.
      * left; exact Hin'.
    + right. exists (S k). split; [lia|]. f_equal. lia.
Qed.

Lemma NoDup_access_pages_acc : forall n base pages,
  List.NoDup pages -> List.NoDup (access_pages_acc base n pages).
Proof.
  induction n as [|n IH]; cbn [access_pages_acc]; intros base pages H; [exact H|].
  apply IH. apply NoDup_page_insert. exact H.
Qed.

Lemma accesses_pages_in : forall accs pages p,
  In p (accesses_pages accs pages) ->
  In p pages
  \/ exists a n k, In (a, n) accs /\ (k < n)%nat /\ p = page_base (boff a k).
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages p H.
  - left; exact H.
  - destruct (IH _ p H) as [Hin | (a' & n' & k & Hin & Hk & Hp)].
    + destruct (access_pages_acc_in n (bv_unsigned a) pages p Hin) as [Hp | (k & Hk & Hp)].
      * left; exact Hp.
      * right. exists a, n, k. rewrite <- page_base_of_boff.
        split; [left; reflexivity | split; assumption].
    + right. exists a', n', k. split; [right; exact Hin | split; assumption].
Qed.

Lemma NoDup_accesses_pages : forall accs pages,
  List.NoDup pages -> List.NoDup (accesses_pages accs pages).
Proof.
  induction accs as [|[a n] accs IH]; cbn [accesses_pages]; intros pages H; [exact H|].
  apply IH. apply NoDup_access_pages_acc. exact H.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Account.
Variable segs : list Segment.
Context {ACEIL : Ceil}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition LINV (g : lghost) (mo : Model) (mat : list word) (mv mr : mem) : Prop :=
  (no_wx segs /\ LOK segs mo) /\ BINV mo g /\ lrel segs mo (g_win g) mv mr /\ (matok (g_win g) mat /\ vdom segs mo mv).

Lemma LINV_LOK : forall g mo mat mv mr, LINV g mo mat mv mr -> LOK segs mo.
Proof. intros g mo mat mv mr [[_ H] _]. exact H. Qed.
Lemma LINV_BINV : forall g mo mat mv mr, LINV g mo mat mv mr -> BINV mo g.
Proof. intros g mo mat mv mr (_ & H & _). exact H. Qed.
Lemma LINV_lrel : forall g mo mat mv mr, LINV g mo mat mv mr -> lrel segs mo (g_win g) mv mr.
Proof. intros g mo mat mv mr (_ & _ & H & _). exact H. Qed.
Lemma LINV_matok : forall g mo mat mv mr, LINV g mo mat mv mr -> matok (g_win g) mat.
Proof. intros g mo mat mv mr (_ & _ & _ & H & _). exact H. Qed.
Lemma LINV_vdom : forall g mo mat mv mr, LINV g mo mat mv mr -> vdom segs mo mv.
Proof. intros g mo mat mv mr (_ & _ & _ & _ & H). exact H. Qed.
Lemma LINV_no_wx : forall g mo mat mv mr, LINV g mo mat mv mr -> no_wx segs.
Proof. intros g mo mat mv mr [[H _] _]. exact H. Qed.

Lemma materialize_accesses_eq : forall L mat used limit acc,
  let new := newly_materialized_pages L mat acc in
  used + Z.of_nat (length new) * page_size <= limit ->
  materialize_accesses L mat used limit acc = Some (new ++ mat).
Proof.
  intros L mat used limit acc new Hb. unfold materialize_accesses. fold new.
  destruct new as [|p new'] eqn:E; [reflexivity|].
  rewrite (proj2 (Z.leb_le _ _) Hb). reflexivity.
Qed.

(* [comment removed for export] *)
Theorem lmaterialize : forall g mo mat mv mr acc,
  LINV g mo mat mv mr ->
  (forall a n, In (a, n) acc -> forall k, (k < n)%nat -> vis segs mv (boff a k)) ->
  let new := newly_materialized_pages (m_vm_lazy mo) mat acc in
  materialize_model_accesses (real mo mat) acc = Some (real mo (new ++ mat))
  /\ LINV g mo (new ++ mat) mv mr.
Proof.
  intros g mo mat mv mr acc ([HWX HO] & HB & [Hm Hhid] & [HM HVD]) Hacc.
  pose proof (lok_lazy_noseg _ _ HO) as HL.
  cbv zeta. set (L := m_vm_lazy mo) in *. set (G := g_win g) in *.
  set (new := newly_materialized_pages L mat acc).
  assert (Hnew_in : forall p, In p new -> In p (gpages G) /\ ~ In p mat).
  { intros p Hp. unfold new, newly_materialized_pages in Hp. apply filter_In in Hp as [Hp Hf].
    apply andb_true_iff in Hf as [Hpl Hpm].
    split.
    2:{ intros Hin. apply page_mem_In in Hin. rewrite Hin in Hpm. discriminate. }
    destruct (accesses_pages_in acc [] p Hp) as [[] | (a & n & k & Hin & Hk & ->)].
    set (x := boff a k) in *.
    pose proof (page_in_ranges_bytes L x Hpl) as Hlx.
    assert (Hvx : mv x <> None).
    { destruct (Hacc a n Hin k Hk) as [Hv | Hs]; [exact Hv|]. exfalso. apply Hs. apply HL. exact Hlx. }
    apply gpages_in; [exact (proj1 HB)|].
    destruct (in_winb G x) eqn:Ew; [reflexivity|]. exfalso. apply Hvx. apply Hhid; assumption. }
  assert (Hnd_new : List.NoDup new).
  { unfold new, newly_materialized_pages. apply NoDup_filter. apply NoDup_accesses_pages. constructor. }
  assert (HM' : matok G (new ++ mat)).
  { destruct HM as [Hnd Hin]. split.
    - apply NoDup_app; [exact Hnd_new | exact Hnd |]. intros p Hp. exact (proj2 (Hnew_in p Hp)).
    - intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (proj1 (Hnew_in p Hp)) | apply Hin; exact Hp]. }
  assert (Hbud : vm_backing_used (real mo mat) + Z.of_nat (length new) * page_size <= vm_limit (m_vmmaps (real mo mat))).
  { rewrite real_used, real_vmmaps. pose proof (matok_length G (new ++ mat) HM') as Hlen.
    rewrite length_app, Nat2Z.inj_add in Hlen. destruct HB as (_ & HR0 & HBB). fold G in HBB.
    rewrite page_size_eq. nia. }
  split.
  - unfold materialize_model_accesses. rewrite real_lazy, real_mat. fold L.
    rewrite (materialize_accesses_eq L mat _ _ acc Hbud). unfold real. rewrite wvb_wvb. reflexivity.
  - split; [split; [exact HWX| exact HO]|]. split; [exact HB|]. split; [split; [exact Hm| exact Hhid]|]. split; [exact HM'| exact HVD].
Qed.

Theorem laccount_step : forall g mo mat ms mr ms1,
  LINV g mo mat (ms_mem ms) mr ->
  RiscvSemantics.step segs ms = MachineOk ms1 ->
  exists mr' acc,
    let new := newly_materialized_pages (m_vm_lazy mo) mat acc in
    RiscvSemantics.step_accesses segs (msw ms mr) = MachineOk (@mkAccessReport _ (msw ms1 mr') acc)
    /\ mi_account_step segs (msw ms mr) (real mo mat) = MachineOk (msw ms1 mr', real mo (new ++ mat))
    /\ LINV g mo (new ++ mat) (ms_mem ms1) mr'.
Proof.
  intros g mo mat ms mr ms1 ([HWX HO] & HB & HR & [HM HVD]) Hstep.
  pose proof (lok_lazy_noseg _ _ HO) as HL.
  destruct HR as [Hm Hhid].
  destruct (step_accesses_ext segs (lzf mo) (lexc mo (g_win g)) (lok_zf_noseg _ _ HO) HWX ms mr ms1 Hm Hstep)
    as (mr' & acc & Hsa & Hm' & Hmono & Hnew & Hacc).
  exists mr', acc. cbv zeta. split; [exact Hsa|].
  set (L := m_vm_lazy mo) in *. set (G := g_win g) in *.
  set (new := newly_materialized_pages L mat acc).
  (* [comment removed for export] *)
  assert (Hhid' : forall x, in_rangesb L x = true -> in_winb G x = false -> ms_mem ms1 x = None).
  { intros x Hl Hw. destruct (ms_mem ms1 x) eqn:Ex; [|reflexivity]. exfalso.
    destruct (Hnew x ltac:(congruence)) as [Hv | Hs].
    - apply Hv. apply Hhid; assumption.
    - apply Hs. apply HL. exact Hl. }
  (* [comment removed for export] *)
  assert (Hnew_in : forall p, In p new -> In p (gpages G) /\ ~ In p mat).
  { intros p Hp. unfold new, newly_materialized_pages in Hp. apply filter_In in Hp as [Hp Hf].
    apply andb_true_iff in Hf as [Hpl Hpm].
    split.
    2:{ intros Hin. apply page_mem_In in Hin. rewrite Hin in Hpm. discriminate. }
    destruct (accesses_pages_in acc [] p Hp) as [[] | (a & n & k & Hin & Hk & ->)].
    set (x := boff a k) in *.
    pose proof (page_in_ranges_bytes L x Hpl) as Hlx.
    assert (Hvx : ms_mem ms1 x <> None).
    { destruct (Hacc a n Hin k Hk) as [Hv | Hs]; [exact Hv|]. exfalso. apply Hs. apply HL. exact Hlx. }
    apply gpages_in; [exact (proj1 HB)|].
    destruct (in_winb G x) eqn:Ew; [reflexivity|]. exfalso. apply Hvx. apply Hhid'; assumption. }
  assert (Hnd_new : List.NoDup new).
  { unfold new, newly_materialized_pages. apply NoDup_filter. apply NoDup_accesses_pages. constructor. }
  assert (HM' : matok G (new ++ mat)).
  { destruct HM as [Hnd Hin]. split.
    - apply NoDup_app; [exact Hnd_new | exact Hnd |]. intros p Hp. exact (proj2 (Hnew_in p Hp)).
    - intros p Hp. apply in_app_or in Hp as [Hp|Hp]; [exact (proj1 (Hnew_in p Hp)) | apply Hin; exact Hp]. }
  (* [comment removed for export] *)
  assert (Hbud : vm_backing_used (real mo mat) + Z.of_nat (length new) * page_size <= vm_limit (m_vmmaps (real mo mat))).
  { rewrite real_used, real_vmmaps. pose proof (matok_length G (new ++ mat) HM') as Hlen.
    rewrite length_app, Nat2Z.inj_add in Hlen. destruct HB as (_ & HR0 & HBB). fold G in HBB.
    rewrite page_size_eq. nia. }
  split.
  - unfold mi_account_step. rewrite Hsa. cbn [accessed_ranges access_value].
    unfold materialize_model_accesses. rewrite real_lazy, real_mat. fold L.
    rewrite (materialize_accesses_eq L mat _ _ acc Hbud). unfold real. rewrite wvb_wvb. reflexivity.
  - split; [split; [exact HWX| exact HO]|]. split; [exact HB|]. split; [split; [exact Hm'| exact Hhid']|]. split; [exact HM'|].
    intros x Hx. destruct (Hnew x Hx) as [Hv|Hs]; [exact (HVD x Hv)| right; left; exact Hs].
Qed.

(* [comment removed for export] *)
Lemma lnode_instr : forall g mo mat ms mr ms1,
  LINV g mo mat (ms_mem ms) mr ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms1 ->
  exists mr' mat',
    LINV g mo mat' (ms_mem ms1) mr'
    /\ node_ok segs (mkCfg (msw ms mr) (real mo mat)) unit (fun _ => [])
               (fun _ => mkCfg (msw ms1 mr') (real mo mat')).
Proof.
  intros g mo mat ms mr ms1 HI Hsvc Hstep.
  destruct (laccount_step g mo mat ms mr ms1 HI Hstep) as (mr' & acc & Hsa & Hacc & HI').
  cbv zeta in Hacc, HI'.
  eexists mr', _. split; [exact HI'|].
  pose proof (lok_halt _ _ (LINV_LOK _ _ _ _ _ HI)) as Hh.
  split.
  - intros []. apply sstep_cfg_instr; [rewrite real_halted; exact Hh | rewrite ms_svc_pending_msw; exact Hsvc | exact Hacc].
  - intros e st Hss. apply sstep_cfg_sub in Hss. inversion Hss; subst;
      try (exfalso; cbn in *; congruence).
    + match goal with H : mi_account_step _ _ _ = MachineOk _ |- _ => rewrite Hacc in H; injection H; intros; subst end.
      exists tt. split; reflexivity.
Qed.

Lemma srz_lstep : forall g mo mat ms mr ms1 T,
  LINV g mo mat (ms_mem ms) mr ->
  ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms1 ->
  (forall mr' mat', LINV g mo mat' (ms_mem ms1) mr' -> srealizes segs (mkCfg (msw ms1 mr') (real mo mat')) T) ->
  srealizes segs (mkCfg (msw ms mr) (real mo mat)) T.
Proof.
  intros g mo mat ms mr ms1 T HI Hsvc Hstep K.
  destruct (lnode_instr g mo mat ms mr ms1 HI Hsvc Hstep) as (mr' & mat' & HI' & Hnode).
  eapply srz_silent1; [exact Hnode| apply K; exact HI'].
Qed.

(* [comment removed for export] *)
Theorem srz_lmsteps : forall ms ms', msteps segs ms ms' -> forall g mo mat mr T,
  LINV g mo mat (ms_mem ms) mr ->
  (forall mr' mat', LINV g mo mat' (ms_mem ms') mr' -> srealizes segs (mkCfg (msw ms' mr') (real mo mat')) T) ->
  srealizes segs (mkCfg (msw ms mr) (real mo mat)) T.
Proof.
  intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH]; intros g mo mat mr T HI K.
  - apply K. exact HI.
  - eapply srz_lstep; [exact HI| exact Hsvc| exact Hstep|]. intros mr' mat' HI'. eapply IH; [exact HI'| exact K].
Qed.

(* [comment removed for export] *)
Theorem lmsteps_star : forall ms ms', msteps segs ms ms' -> forall g mo mat mr,
  LINV g mo mat (ms_mem ms) mr ->
  exists mr' mat', LINV g mo mat' (ms_mem ms') mr'
    /\ star segs (mkCfg (msw ms mr) (real mo mat)) [] (mkCfg (msw ms' mr') (real mo mat')).
Proof.
  intros ms ms' Hms. induction Hms as [ms | ms ms1 ms2 [Hsvc Hstep] Hms IH]; intros g mo mat mr HI.
  - exists mr, mat. split; [exact HI| apply star_refl].
  - destruct (laccount_step g mo mat ms mr ms1 HI Hstep) as (mr1 & acc & _ & Hacc & HI1). cbv zeta in Hacc, HI1.
    destruct (IH g mo _ mr1 HI1) as (mr' & mat' & HI' & Hstar).
    exists mr', mat'. split; [exact HI'|].
    change ([] : list event) with ([] ++ [] : list event).
    eapply star_step; [| exact Hstar].
    apply sstep_instr; [rewrite real_halted; exact (lok_halt _ _ (LINV_LOK _ _ _ _ _ HI)) | rewrite ms_svc_pending_msw; exact Hsvc | exact Hacc].
Qed.

(* [comment removed for export] *)
Lemma to_spin_j_real : forall ms mr mo mat w (rd : reg) (imm : bv 21) sz,
  ms_svc_pending ms = None ->
  fetch_word segs (ms_pc ms) = Some w -> is_ecall w = false ->
  decode_any w = Some (Jal rd imm, sz) -> is_x0 rd = true -> bv_signed imm = 0%Z ->
  to_spin segs (msw ms mr) (real mo mat).
Proof.
  intros. eapply ts_spin_of_step_j; eassumption.
Qed.

End Account.
End LStep.

(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil PropExec MState Mem Cells Step Frame Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
Import LStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition open_mem (zf : word -> bool) (lo hi : Z) (mv : mem) : mem :=
  fun x => match mv x with
           | Some b => Some b
           | None => if ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi) && zf x)%bool
                     then Some b0 else None
           end.

Lemma open_mem_some : forall zf lo hi mv x b, mv x = Some b -> open_mem zf lo hi mv x = Some b.
Proof. intros zf lo hi mv x b H. unfold open_mem. rewrite H. reflexivity. Qed.

Lemma open_mem_mono : forall zf lo hi mv x, mv x <> None -> open_mem zf lo hi mv x = mv x.
Proof. intros zf lo hi mv x H. unfold open_mem. destruct (mv x); [reflexivity| congruence]. Qed.

Lemma open_mem_fresh : forall zf lo hi mv x,
  mv x = None -> lo <= bv_unsigned x < hi -> zf x = true -> open_mem zf lo hi mv x = Some b0.
Proof.
  intros zf lo hi mv x Hm Hr Hl. unfold open_mem. rewrite Hm, Hl.
  destruct (Z.leb_spec0 lo (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) hi); cbn; try reflexivity; lia.
Qed.

Lemma open_mem_vis : forall zf lo hi mv x,
  lo <= bv_unsigned x < hi -> zf x = true -> open_mem zf lo hi mv x <> None.
Proof.
  intros zf lo hi mv x Hr Hl. unfold open_mem. destruct (mv x); [discriminate|]. rewrite Hl.
  destruct (Z.leb_spec0 lo (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) hi); cbn; try discriminate; lia.
Qed.

Lemma open_mem_outside : forall zf lo hi mv x,
  open_mem zf lo hi mv x <> mv x -> mv x = None /\ lo <= bv_unsigned x < hi /\ zf x = true.
Proof.
  intros zf lo hi mv x H. unfold open_mem in H. destruct (mv x); [congruence|].
  destruct (Z.leb_spec0 lo (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) hi);
    destruct (zf x); cbn in H; try congruence. auto.
Qed.

Lemma lmem_open_mem : forall (rv zf : word -> bool) lo hi mv,
  (forall x, rv x = true -> zf x = true) ->
  meq (lmem zf (open_mem rv lo hi mv)) (lmem zf mv).
Proof.
  intros rv zf lo hi mv Hrz x. unfold lmem, open_mem. destruct (mv x); [reflexivity|].
  destruct (rv x) eqn:E; [|rewrite andb_false_r; reflexivity].
  rewrite (Hrz x E), andb_true_r. destruct ((lo <=? bv_unsigned x) && (bv_unsigned x <? hi))%bool; reflexivity.
Qed.

(* [comment removed for export] *)
Definition owf (mo : Model) (G : gwin) : word -> bool := fun x => lzf mo x && negb (in_winb G x).

Lemma owf_lzf : forall mo G x, owf mo G x = true -> lzf mo x = true.
Proof. intros mo G x H. unfold owf in H. apply andb_true_iff in H. exact (proj1 H). Qed.
Lemma owf_win : forall mo G x, owf mo G x = true -> in_winb G x = false.
Proof. intros mo G x H. unfold owf in H. apply andb_true_iff in H as [_ H]. destruct (in_winb G x); [discriminate| reflexivity]. Qed.
Lemma owf_intro : forall mo G x, lzf mo x = true -> in_winb G x = false -> owf mo G x = true.
Proof. intros mo G x H1 H2. unfold owf. rewrite H1, H2. reflexivity. Qed.

Section WithSegs.
Variable segs : list Segment.
Context {ACEIL : Ceil}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma mrd_open : forall zf lo hi mv x b, zf_noseg segs zf ->
  mrd segs mv x = Some b -> mrd segs (open_mem zf lo hi mv) x = Some b.
Proof.
  intros zf lo hi mv x b HL H. unfold mrd, open_mem in *. destruct (mv x); [exact H|].
  destruct (zf x) eqn:E.
  - rewrite (seg_rom_noseg segs x (proj1 (HL x E))) in H. discriminate.
  - rewrite andb_false_r. exact H.
Qed.

Lemma wview_open : forall zf lo hi mv x, wview segs mv x <> None -> wview segs (open_mem zf lo hi mv) x <> None.
Proof.
  intros zf lo hi mv x H. unfold wview, open_mem in *. destruct (mv x); [exact H|].
  match goal with |- context [if ?c then Some b0 else None] => destruct c end; [discriminate| exact H].
Qed.

Lemma bytes_at_open : forall zf lo hi mv a bs, zf_noseg segs zf ->
  bytes_at segs mv a bs -> bytes_at segs (open_mem zf lo hi mv) a bs.
Proof.
  intros zf lo hi mv a bs HL (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. pose proof (H i Hi) as Hb.
  destruct (nth_error bs i) as [b|] eqn:E; [| exfalso; apply nth_error_None in E; lia].
  apply mrd_open; assumption.
Qed.

Lemma wr_at_open : forall zf lo hi mv a n, wr_at segs mv a n -> wr_at segs (open_mem zf lo hi mv) a n.
Proof.
  intros zf lo hi mv a n (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros i Hi. apply wview_open. apply H. exact Hi.
Qed.

Lemma rw_cells_open : forall zf lo hi mv a cs, zf_noseg segs zf ->
  rw_cells segs mv a cs -> rw_cells segs (open_mem zf lo hi mv) a cs.
Proof.
  intros zf lo hi mv a cs HL [[Hwf Hb] Hw]. split; [split; [exact Hwf| apply bytes_at_open; assumption]| apply wr_at_open; assumption].
Qed.

Lemma ro_cells_open : forall zf lo hi mv a cs, zf_noseg segs zf ->
  ro_cells segs mv a cs -> ro_cells segs (open_mem zf lo hi mv) a cs.
Proof. intros zf lo hi mv a cs HL [Hwf Hb]. split; [exact Hwf| apply bytes_at_open; assumption]. Qed.

Lemma stk_open : forall zf lo hi mv l h, zf_noseg segs zf ->
  stk segs mv l h -> stk segs (open_mem zf lo hi mv) l h.
Proof.
  intros zf lo hi mv l h HL (H0 & H1 & H). split; [exact H0|]. split; [exact H1|].
  intros a Ha. destruct (H a Ha) as [Hw [b Hb]]. split; [apply wview_open; exact Hw|].
  exists b. apply mrd_open; assumption.
Qed.

Lemma mem_inv_open : forall zf lo hi mv, zf_noseg segs zf ->
  mem_inv segs mv -> mem_inv segs (open_mem zf lo hi mv).
Proof.
  intros zf lo hi mv HL H x b Hx. unfold open_mem in Hx. destruct (mv x) as [c|] eqn:E.
  - eapply H; eauto.
  - destruct (zf x) eqn:E2; [| rewrite andb_false_r in Hx; discriminate].
    right. split; [apply ro_addr_noseg; exact (proj1 (HL x E2)) | exact (proj2 (HL x E2))].
Qed.

Lemma munch_open_r : forall zf lo hi W m (mv : mem), munch W m mv ->
  (forall x : word, lo <= bv_unsigned x < hi -> ~ outside W (bv_unsigned x)) ->
  munch W m (open_mem zf lo hi mv).
Proof.
  intros zf lo hi W m mv HM HW x Hx. rewrite <- (HM x Hx). unfold open_mem.
  destruct (mv x); [reflexivity|].
  destruct (Z.leb_spec0 lo (bv_unsigned x)); destruct (Z.ltb_spec0 (bv_unsigned x) hi); cbn; try reflexivity.
  exfalso. apply (HW x); [lia| exact Hx].
Qed.

Lemma wmono_open : forall zf lo hi m mv, wmono segs m mv -> wmono segs m (open_mem zf lo hi mv).
Proof. intros zf lo hi m mv H x Hx. apply wview_open. apply H. exact Hx. Qed.

(* [comment removed for export] *)
Lemma bytes_at_zeros : forall (mv : mem) a n,
  0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> mv (wa (a + i)) = Some b0) ->
  bytes_at segs mv a (repeat b0 n).
Proof.
  intros mv a n H0 H1 H. split; [exact H0|]. rewrite repeat_length. split; [exact H1|].
  intros i Hi. unfold mrd. rewrite (H (Z.of_nat i)) by lia. symmetry. apply nth_error_repeat. exact Hi.
Qed.

Lemma rw_cells_zeros : forall (mv : mem) a n,
  0 <= a -> a + Z.of_nat n <= 2^64 ->
  (forall i, 0 <= i < Z.of_nat n -> mv (wa (a + i)) = Some b0) ->
  rw_cells segs mv a [CB n (repeat b0 n)].
Proof.
  intros mv a n H0 H1 H. split.
  - split; [cbn; split; [apply repeat_length| exact I]|]. cbn. rewrite app_nil_r. apply bytes_at_zeros; assumption.
  - cbn. rewrite Nat.add_0_r. split; [exact H0|]. split; [exact H1|]. intros i Hi.
    unfold wview. rewrite (H i Hi). discriminate.
Qed.

Lemma ov_read_byte_of : forall (mv : mem) x b, mv x = Some b -> ov_read_bytes segs mv x 1 = Some [b].
Proof. intros mv x b H. cbn. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LSCPS (P : machine_state -> Model -> lghost -> Prop)
           (ms : machine_state) (mo : Model) (g : lghost) : Prop :=
  forall mr mat, LINV segs g mo mat (ms_mem ms) mr ->
  forall T : TSet,
    (forall ms' mo' g' mr' mat',
        P ms' mo' g' -> LINV segs g' mo' mat' (ms_mem ms') mr' -> vm_only mo mo' ->
        srealizes segs (mkCfg (msw ms' mr') (real mo' mat')) T) ->
    srealizes segs (mkCfg (msw ms mr) (real mo mat)) T.

Lemma lscps_done : forall (P : machine_state -> Model -> lghost -> Prop) ms mo g,
  P ms mo g -> LSCPS P ms mo g.
Proof. intros P ms mo g HP mr mat HI T K. apply (K ms mo g mr mat HP HI (vm_only_refl mo)). Qed.

Lemma lscps_mono : forall (P Q : machine_state -> Model -> lghost -> Prop) ms mo g,
  LSCPS P ms mo g -> (forall ms' mo' g', P ms' mo' g' -> Q ms' mo' g') -> LSCPS Q ms mo g.
Proof.
  intros P Q ms mo g H HPQ mr mat HI T K. apply (H mr mat HI). intros ms' mo' g' mr' mat' HP HI' HV.
  eapply K; [apply HPQ, HP | exact HI' | exact HV].
Qed.

Lemma lscps_bind : forall (P Q : machine_state -> Model -> lghost -> Prop) ms mo g,
  LSCPS P ms mo g -> (forall ms' mo' g', P ms' mo' g' -> LSCPS Q ms' mo' g') -> LSCPS Q ms mo g.
Proof.
  intros P Q ms mo g H K mr mat HI T HK. apply (H mr mat HI). intros ms' mo' g' mr' mat' HP HI' HV.
  apply (K ms' mo' g' HP mr' mat' HI'). intros ms2 mo2 g2 mr2 mat2 HQ HI2 HV2.
  eapply HK; [exact HQ | exact HI2 | eapply vm_only_trans; eassumption].
Qed.

Lemma lscps_eq : forall P ms ms' mo g, ms = ms' -> LSCPS P ms' mo g -> LSCPS P ms mo g.
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma lscps_assume : forall (P : machine_state -> Model -> lghost -> Prop) ms mo g,
  (no_wx segs -> LOK segs mo -> BINV mo g -> LSCPS P ms mo g) -> LSCPS P ms mo g.
Proof.
  intros P ms mo g H mr mat HI.
  apply (H (LINV_no_wx _ _ _ _ _ _ HI) (LINV_LOK _ _ _ _ _ _ HI) (LINV_BINV _ _ _ _ _ _ HI) mr mat HI).
Qed.

(* [comment removed for export] *)
Lemma lscps_assume_hidden : forall (P : machine_state -> Model -> lghost -> Prop) ms mo g,
  ((forall x, in_rangesb (m_vm_lazy mo) x = true -> in_winb (g_win g) x = false -> ms_mem ms x = None) ->
   LSCPS P ms mo g) -> LSCPS P ms mo g.
Proof. intros P ms mo g H mr mat HI. apply (H (proj2 (LINV_lrel _ _ _ _ _ _ HI)) mr mat HI). Qed.

(* [comment removed for export] *)
Lemma lscps_frame_post : forall (P : machine_state -> Model -> lghost -> Prop) ms mo g,
  LSCPS P ms mo g ->
  LSCPS (fun ms' mo' g' => P ms' mo' g' /\ vm_only mo mo' /\ LOK segs mo' /\ BINV mo' g') ms mo g.
Proof.
  intros P ms mo g H mr mat HI T K. apply (H mr mat HI). intros ms' mo' g' mr' mat' HP HI' HV.
  eapply K; [| exact HI'| exact HV]. split; [exact HP|]. split; [exact HV|].
  split; [eapply LINV_LOK; exact HI'| eapply LINV_BINV; exact HI'].
Qed.

(* [comment removed for export] *)
Lemma lscps_evt : forall (Q : machine_state -> Prop) ms mo g,
  evt segs Q ms -> LSCPS (fun ms' mo' g' => Q ms' /\ mo' = mo /\ g' = g) ms mo g.
Proof.
  intros Q ms mo g (ms' & Hms & HQ) mr mat HI T K.
  eapply srz_lmsteps; [exact Hms| exact HI|].
  intros mr' mat' HI'. apply (K ms' mo g mr' mat'); [auto| exact HI'| apply vm_only_refl].
Qed.

Lemma lscps_evt_then : forall (Q : machine_state -> Prop) (P : machine_state -> Model -> lghost -> Prop) ms mo g,
  evt segs Q ms -> (forall ms', Q ms' -> LSCPS P ms' mo g) -> LSCPS P ms mo g.
Proof.
  intros Q P ms mo g He K. eapply lscps_bind; [apply lscps_evt; exact He|].
  intros ms' mo' g' (HQ & -> & ->). apply K. exact HQ.
Qed.

(* [comment removed for export] *)
Lemma lscps_step_evt : forall (P : machine_state -> Model -> lghost -> Prop) ms mo g,
  evt segs (fun ms' => LSCPS P ms' mo g) ms -> LSCPS P ms mo g.
Proof. intros P ms mo g He. eapply lscps_evt_then; [exact He|]. intros ms' H; exact H. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lscps_res_le : forall P ms mo G R R',
  0 <= R' <= R -> LSCPS P ms mo (mkG G R') -> LSCPS P ms mo (mkG G R).
Proof.
  intros P ms mo G R R' HR H mr mat (HO & HB & HL & HM) T K.
  apply (H mr mat); [| exact K]. split; [exact HO|]. split; [eapply BINV_res_le; [exact HB| exact HR]|].
  split; [exact HL| exact HM].
Qed.

(* [comment removed for export] *)
Theorem lscps_open : forall (P : machine_state -> Model -> lghost -> Prop) ms mo G R lo hi,
  win_ok (lo, hi) ->
  4096 * ((hi - lo) / 4096) <= R ->
  (forall mv',
      mv' = open_mem (owf mo G) lo hi (ms_mem ms) ->
      zf_noseg segs (owf mo G) ->
      (* [comment removed for export] *)
      (forall x, lo <= bv_unsigned x < hi -> lzf mo x = true ->
                 in_winb G x = false -> mv' x = Some b0) ->
      LSCPS P (msw ms mv') mo (mkG ((lo, hi) :: G) (R - 4096 * ((hi - lo) / 4096)))) ->
  LSCPS P ms mo (mkG G R).
Proof.
  intros P ms mo G R lo hi Hw HR K mr mat ([HWX HO] & HB & [Hm Hhid] & [HM HVD]) T HK.
  set (mv' := open_mem (owf mo G) lo hi (ms_mem ms)).
  assert (HZS : zf_noseg segs (owf mo G)).
  { intros x Hx. apply (lok_zf_noseg _ _ HO). apply owf_lzf with (G := G). exact Hx. }
  assert (HI' : LINV segs (mkG ((lo, hi) :: G) (R - 4096 * ((hi - lo) / 4096))) mo mat mv' mr).
  { split; [split; [exact HWX| exact HO]|]. split; [apply BINV_open; assumption|]. split.
    - split.
      + intros x. destruct (Hm x) as [E | (E1 & E2 & E3)].
        * left. rewrite E. symmetry. apply (lmem_open_mem (owf mo G) (lzf mo)). apply owf_lzf.
        * unfold mv', open_mem. rewrite E1. cbn [g_win] in E3. destruct E3 as [E3 | E3].
          -- right. unfold owf. rewrite E3. cbn [andb]. rewrite andb_false_r. split; [reflexivity|]. split; [exact E2| left; exact E3].
          -- right. unfold owf. rewrite E3. cbn [negb]. rewrite !andb_false_r. split; [reflexivity|]. split; [exact E2|].
             right. cbn [g_win]. rewrite in_winb_cons, E3. apply orb_true_r.
      + cbn [g_win]. intros x Hl Hw'. rewrite in_winb_cons in Hw'. apply orb_false_iff in Hw' as [Hr Hw'].
        cbn [fst snd] in Hr. unfold mv', open_mem. rewrite (Hhid x Hl Hw'). rewrite Hr. reflexivity.
    - cbn [g_win]. split; [apply matok_open; exact HM|].
      intros x Hx. unfold mv' in Hx. destruct (ms_mem ms x) eqn:Ex.
      + apply HVD. congruence.
      + assert (Hne : open_mem (owf mo G) lo hi (ms_mem ms) x <> ms_mem ms x) by congruence.
        destruct (open_mem_outside (owf mo G) lo hi (ms_mem ms) x Hne) as (_ & _ & Hz).
        right; right. apply (lok_lazy_maps _ _ HO). apply lzf_lazy. apply owf_lzf with (G := G). exact Hz. }
  pose proof (K mv' eq_refl HZS) as K'.
  assert (Hz : forall x, lo <= bv_unsigned x < hi -> lzf mo x = true ->
               in_winb G x = false -> mv' x = Some b0).
  { intros x Hr Hl Hw'. unfold mv'. apply open_mem_fresh; [apply Hhid; [apply lzf_lazy; exact Hl| exact Hw']| exact Hr| apply owf_intro; assumption]. }
  specialize (K' Hz mr mat). rewrite msw_msw in K'. cbn [ms_mem msw] in K'.
  apply (K' HI' T). intros ms2 mo2 g2 mr2 mat2 HP HI2 HV. eapply HK; eassumption.
Qed.

(* [comment removed for export] *)

Theorem lscps_srealizes : forall (P : machine_state -> Model -> lghost -> Prop) ms mo g mr mat T,
  LSCPS P ms mo g ->
  LINV segs g mo mat (ms_mem ms) mr ->
  (forall ms' mo' g' mr' mat', P ms' mo' g' -> LINV segs g' mo' mat' (ms_mem ms') mr' -> vm_only mo mo' ->
      srealizes segs (mkCfg (msw ms' mr') (real mo' mat')) T) ->
  srealizes segs (mkCfg (msw ms mr) (real mo mat)) T.
Proof. intros P ms mo g mr mat T H HI K. exact (H mr mat HI T K). Qed.

(* [comment removed for export] *)
Definition hide_mem (L : list (word * word)) (G : gwin) (mr : mem) : mem :=
  fun x => if (in_rangesb L x && negb (in_winb G x))%bool then None else mr x.

Theorem LINV_intro : forall g mo mv mr,
  no_wx segs -> LOK segs mo -> BINV mo g ->
  matok (g_win g) (m_vm_materialized mo) ->
  magree segs (lzf mo) (lexc mo (g_win g)) mv mr ->
  (forall x, in_rangesb (m_vm_lazy mo) x = true -> in_winb (g_win g) x = false -> mv x = None) ->
  vdom segs mo mv ->
  LINV segs g mo (m_vm_materialized mo) mv mr.
Proof.
  intros g mo mv mr HWX HO HB HM Hm Hhid HVD. split; [split; assumption|]. split; [exact HB|].
  split; [split; [exact Hm| exact Hhid]|]. split; [exact HM| exact HVD].
Qed.

Lemma real_of_self : forall mo, real mo (m_vm_materialized mo) = mo.
Proof. apply real_self. Qed.

End WithSegs.

Arguments LSCPS segs {ACEIL} P ms mo g /.   (* [comment removed for export] *)
