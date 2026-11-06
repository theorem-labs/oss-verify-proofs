(** Segments M02 and V01 of reac-pw/fuzz_segconf LLVMFuzzerTestOneInput: the spine
    facts both builds' walks of M02 and V01 read, build-independent (the UBSan walks Require this file).
    - mb_bytes_ok, mb_harness_ok: the payload of every input passes every check (SegModel.segconf_agrees on the
      input's bytes, seg_spec.seg_in).
    - mb_checks: harness_ok split into the seven checks, over the state after the file loop (the state the cut
      predicates P_K13ae0 / P_K13cac name: seg_rc, seg_mc, seg_ret of SegModel.run (seg_pay inp)).
    - mb_run_rel: that state's reader and model are related (SegModel.conf_rel) and its [returned] is true
      (SegModel.run_rel), so every name, flag and count the checks compare agree.
    Spine lemma for the segment walks of LLVMFuzzerTestOneInput. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require Import SegModel.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Prog Require Import seg_spec.
Import ListNotations.
Open Scope Z_scope.

Lemma mb_bytes_ok : forall inp : list byte, Forall (fun b => 0 <= b < 256) (seg_in inp).
Proof.
  intros inp. unfold seg_in, zs. apply Forall_map, Forall_forall. intros b _.
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. exact R.
Qed.

Lemma mb_harness_ok : forall inp : list byte, harness_ok (seg_pay inp) = true.
Proof. intros inp. exact (segconf_agrees (seg_in inp) (mb_bytes_ok inp)). Qed.

Lemma mb_checks_of : forall p, harness_ok p = true ->
  check_segments (seg_rc (run p)) (seg_mc (run p)) (seg_ret (run p)) = true /\
  forallb (check_seg (seg_rc (run p))) (mc_seg (seg_mc (run p))) = true /\
  check_refusals (seg_rc (run p)) (seg_mc (run p)) = true /\
  check_kept_all (rc_refusal (seg_rc (run p))) (mc_kept (seg_mc (run p))) = true /\
  forallb (fun g => probe_ok (seg_rc (run p)) (seg_mc (run p)) (snprintf_s 18 F_probe [AS (ms_name g)]))
    (mc_seg (seg_mc (run p))) = true /\
  probe_ok (seg_rc (run p)) (seg_mc (run p)) S_nosuch = true /\
  vlans_are (r_declared (seg_rc (run p)) (vlan_init p) (p_cap p))
            (m_declared (seg_mc (run p)) (vlan_init p) (p_cap p)) (p_cap p) = true.
Proof.
  intros p H. unfold harness_ok in H. revert H. unfold seg_rc, seg_mc, seg_ret.
  destruct (run p) as [[c m] ret]. cbn [fst snd]. intros H. cbv beta iota zeta in H.
  apply andb_true_iff in H as [H H7]. apply andb_true_iff in H as [H H6].
  apply andb_true_iff in H as [H H5]. apply andb_true_iff in H as [H H4].
  apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
  repeat split; assumption.
Qed.

Lemma mb_checks : forall inp : list byte,
  check_segments (seg_rc (run (seg_pay inp))) (seg_mc (run (seg_pay inp))) (seg_ret (run (seg_pay inp))) = true /\
  forallb (check_seg (seg_rc (run (seg_pay inp)))) (mc_seg (seg_mc (run (seg_pay inp)))) = true /\
  check_refusals (seg_rc (run (seg_pay inp))) (seg_mc (run (seg_pay inp))) = true /\
  check_kept_all (rc_refusal (seg_rc (run (seg_pay inp)))) (mc_kept (seg_mc (run (seg_pay inp)))) = true /\
  forallb (fun g => probe_ok (seg_rc (run (seg_pay inp))) (seg_mc (run (seg_pay inp)))
                      (snprintf_s 18 F_probe [AS (ms_name g)]))
    (mc_seg (seg_mc (run (seg_pay inp)))) = true /\
  probe_ok (seg_rc (run (seg_pay inp))) (seg_mc (run (seg_pay inp))) S_nosuch = true /\
  vlans_are (r_declared (seg_rc (run (seg_pay inp))) (seg_tab0 inp) (seg_cap inp))
            (m_declared (seg_mc (run (seg_pay inp))) (seg_tab0 inp) (seg_cap inp)) (seg_cap inp) = true.
Proof. intros inp. exact (mb_checks_of (seg_pay inp) (mb_harness_ok inp)). Qed.

Lemma mb_run_rel : forall inp : list byte,
  conf_rel (seg_rc (run (seg_pay inp))) (seg_mc (run (seg_pay inp))) /\ seg_ret (run (seg_pay inp)) = true.
Proof.
  intros inp. destruct (decode_ok (seg_in inp) (mb_bytes_ok inp)) as [Hf _].
  unfold seg_pay, run, seg_rc, seg_mc, seg_ret.
  pose proof (run_rel (p_files (decode (seg_in inp))) rconf0 mconf0 true conf_rel0 Hf) as Hr.
  revert Hr. destruct (run_files (p_files (decode (seg_in inp))) rconf0 mconf0 true) as [[c m] ret].
  intros [Hc ->]. cbn [fst snd]. split; [exact Hc | reflexivity].
Qed.

Lemma mb_cap : forall inp : list byte, 0 <= seg_cap inp < 40.
Proof.
  intros inp. unfold seg_cap, seg_pay, decode.
  destruct (fuzz_u8 (seg_in inp)) as [b0 i1]. destruct (fuzz_u8 i1) as [fl i2]. destruct (fuzz_u8 i2) as [b2 i3].
  cbn [p_cap]. Z.div_mod_to_equations. lia.
Qed.
