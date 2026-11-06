From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Prog Require Import fuzz_alloc_fail_c.
Import ListNotations.
Open Scope Z_scope.

Local Ltac OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib.Step.mem_after_store_opt ::= idtac.

Lemma wfin : forall m o bs, 0 <= o -> o + Z.of_nat (length bs) <= 2^64 ->
  bytes_at rsegs (write_to_mem m (wa o) bs) o bs /\
  munch [(o, o + Z.of_nat (length bs))] m (write_to_mem m (wa o) bs) /\
  wmono rsegs m (write_to_mem m (wa o) bs).
Proof.
  intros m o bs H1 H2. split; [apply bytes_at_write_same; lia|]. split.
  - apply munch_write; [apply munch_refl | lia | lia | cbn; left; lia].
  - apply wmono_write, wmono_refl.
Qed.

Lemma lor_ones64 : forall x, 0 <= x < 2^64 -> Z.lor (2^64 - 1) x = 2^64 - 1.
Proof.
  intros x Hx. change (2^64 - 1) with (Z.ones 64). apply Z.bits_inj'. intros i Hi. rewrite Z.lor_spec.
  destruct (Z.lt_ge_cases i 64) as [Hl|Hg].
  - rewrite Z.ones_spec_low by lia. reflexivity.
  - rewrite Z.ones_spec_high by lia. cbn [orb].
    rewrite <- (Z.mod_small x (2^64)) by lia. apply Z.mod_pow2_bits_high. lia.
Qed.

Lemma fail_val : forall count k : word,
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (0 - bv_unsigned (v_sltu (Z_to_bv 64 (bv_unsigned count + bv_unsigned k)) count))))
                    (bv_unsigned (Z_to_bv 64 (bv_unsigned count + bv_unsigned k))))
  = fail_at_of count k.
Proof.
  intros count k. rewrite v_sltu_b2z. unfold fail_at_of.
  pose proof (bv_unsigned_in_range 64 count) as Hc. pose proof (bv_unsigned_in_range 64 k) as Hk.
  unfold bv_modulus in Hc, Hk. change (2 ^ Z.of_N 64) with (2^64) in Hc, Hk.
  rewrite !unsigned_lit_wrap.
  destruct (Z.ltb_spec (bv_unsigned count + bv_unsigned k) (2^64)) as [H|H].
  - rewrite (Z.mod_small (bv_unsigned count + bv_unsigned k)) by lia.
    rewrite (proj2 (Z.ltb_ge (bv_unsigned count + bv_unsigned k) (bv_unsigned count))) by lia.
    cbn [Z.b2z]. change ((0 - 0 mod 2 ^ 64) mod 2 ^ 64) with 0. rewrite Z.lor_0_l. reflexivity.
  - assert (E : (bv_unsigned count + bv_unsigned k) mod 2^64 = bv_unsigned count + bv_unsigned k - 2^64).
    { symmetry. apply (Z.mod_unique _ _ 1); lia. }
    rewrite E. rewrite (proj2 (Z.ltb_lt (bv_unsigned count + bv_unsigned k - 2^64) (bv_unsigned count))) by lia.
    cbn [Z.b2z]. change ((0 - 1 mod 2^64) mod 2^64) with (2^64 - 1).
    rewrite lor_ones64 by lia. reflexivity.
Qed.

Theorem fuzz_alloc_fail_holds : fuzz_alloc_fail_contract.
Proof.
  unfold fuzz_alloc_fail_contract, FUZZ_ALLOC_FAIL, G_COUNT, G_FAIL_AT.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m count HC W.
  assert (RD : ov_read_bytes rsegs m (wa 0x2f380) 8 = Some (le8 count)).
  { replace (wa 0x2f380) with (wa (0x2f380 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x2f380 (le8 count) 0 8 HC ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  pose proof W as (Wo & Wn & _).
  assert (HS : store_ok rsegs m (wa (0x1f0f8 + 0)) 8 = true) by (eapply wr_at_store_ok; [exact W | lia | lia]).
  do 9 step.
  rewrite !fail_val.
  apply evt_done. do 2 eexists. split; [reflexivity|].
  rewrite ?Z.add_0_r. apply wfin; cbn [length]; rewrite ?length_le8; lia.
Qed.
