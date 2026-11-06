From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import reac_rate_snap_c.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_read0 : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof H as (H0 & H1 & _).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia.
  f_equal. apply firstn_all.
Qed.

Ltac step_keep :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) =>
    let fw := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
    lazymatch fw with
    | Some ?w =>
      let d := eval vm_compute in (decode_any w) in
      lazymatch d with
      | Some (?i, ?sz) =>
        eapply evt_step;
        [ split; [reflexivity|];
          rewrite (step_gen segs R F (Z_to_bv 64 pc) fc rv m ro w i sz) by (vm_compute; reflexivity);
          exec_pre i;
          exec_cbv; simp_is_x0; simp_regs; vnorm_for i;
          try solve_load; try solve_store;
          reflexivity
        | simp_regs; vnorm_for i ]
      end
    end
  end.

Ltac key_to K n := assert (EK : K = Z_to_bv 5 n) by (first [reflexivity | apply bv_eq; reflexivity]); rewrite EK; clear EK.

Lemma fcsr_nan : forall (x : word) (fc : bv 32),
  Z_to_bv 32 (Z.lor (bv_unsigned (Z_to_bv 32 (Z.lor (bv_unsigned fc)
                     (fflags_bits (fcmp_fl F_LT fmt_double (bv_unsigned x) 4663319084467748864)))))
                    (fflags_bits (fcmp_fl F_LT fmt_double (bv_unsigned x) 4660657166816903168)))
  = Z_to_bv 32 (Z.lor (bv_unsigned fc) (if fp_is_nan fmt_double (bv_unsigned x) then 16 else 0)).
Proof.
  intros x fc. cbv beta iota delta [fcmp_fl fcmp_sem fp_lt]. cbn [snd].
  replace (fp_is_nan fmt_double 4663319084467748864) with false by (vm_compute; reflexivity).
  replace (fp_is_nan fmt_double 4660657166816903168) with false by (vm_compute; reflexivity).
  rewrite !orb_false_r.
  pose proof (bv_unsigned_in_range 32 fc) as Hf. unfold bv_modulus in Hf.
  destruct (fp_is_nan fmt_double (bv_unsigned x)).
  - replace (fflags_bits nv_flag) with 16 by reflexivity.
    assert (HR : 0 <= Z.lor (bv_unsigned fc) 16 < 2^32) by (apply Z_lor_lt_pow2; lia).
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia).
    rewrite <- Z.lor_assoc, Z.lor_diag. reflexivity.
  - replace (fflags_bits no_flags) with 0 by reflexivity. rewrite !Z.lor_0_r.
    rewrite Z_to_bv_unsigned, bv_wrap_small by (unfold bv_modulus; lia). reflexivity.
Qed.

Theorem reac_rate_snap_holds : reac_rate_snap_contract.
Proof.
  unfold reac_rate_snap_contract, REAC_RATE_SNAP, reac_rate_snap_model, reac_rate_snap_fcsr, A_P6000, A_P3837.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HA HB.
  pose proof (bytes_at_read0 m _ _ HA) as RA. change (ov_read_bytes rsegs m (wa 0x104f0) 8 = Some (le8 (Z_to_bv 64 D6000))) in RA.
  pose proof (bytes_at_read0 m _ _ HB) as RB. change (ov_read_bytes rsegs m (wa 0x10558) 8 = Some (le8 (Z_to_bv 64 D3837))) in RB.
  unfold D6000, D3837 in *.
  step. step. step. step. step_keep. step_keep.
  repeat match goal with |- context [Sem.reg_get F ?K] => tryif constr_eq K (Z_to_bv 5 10) then fail else key_to K 10 end.
  match goal with |- context [bvmap_set ?K _ (bvmap_set _ _ F)] => key_to K 14 end.
  match goal with |- context [bvmap_set _ _ (bvmap_set ?K _ F)] => key_to K 15 end.
  destruct (flt_d (Sem.reg_get F (Z_to_bv 5 10)) (Z_to_bv 64 4663319084467748864)) eqn:C1;
  destruct (flt_d (Sem.reg_get F (Z_to_bv 5 10)) (Z_to_bv 64 4660657166816903168)) eqn:C2;
  repeat first [ if_true | if_false | step ];
  rewrite fcsr_nan; apply evt_done; eexists; reflexivity.
Qed.
