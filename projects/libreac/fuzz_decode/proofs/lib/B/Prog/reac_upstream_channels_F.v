From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_upstream_channels_c reac_upstream_channels.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import reac_upstream_channels_F_c.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Lib Require Import ExecF StepF.
Import ListNotations.
Open Scope Z_scope.

(* The proof of reac_upstream_channels_holds (reac_upstream_channels.v) step for step, with StepF's step; the
   arithmetic lemmas (upstream_small, div36_magic, shr64_range, sltiu_w, tail_bad, tail_good, even_mod32) are the
   ones of reac_upstream_channels.v. The one data access, the 8-byte load at 0x10338 (ld at 0x81ff8), is closed
   from the rng premise RK. *)
Theorem reac_upstream_channels_holds_F : reac_upstream_channels_contract_F.
Proof.
  unfold reac_upstream_channels_contract_F, REAC_UPSTREAM_CHANNELS, UPSTREAM_DIV36_AT, UPSTREAM_DIV36.
  intros RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    HK RK.
  assert (RD : ov_read_bytes rsegs m (wa 0x10338) 8 = Some (le8 (Z_to_bv 64 0xe38e38e38e38e38f))).
  { replace (wa 0x10338) with (wa (0x10338 + 0)) by reflexivity.
    rewrite (bytes_at_read rsegs m 0x10338 _ 0 8 HK ltac:(lia)) by (rewrite length_le8; lia).
    reflexivity. }
  pose proof (bv_unsigned_in_range 64 a0) as RA. unfold bv_modulus in RA.
  step. step. step.
  if_cases HL.
  - zify_cond HL.
    step. step. apply evtF_done.
    rewrite upstream_small by lia. do 3 eexists. reflexivity.
  - zify_cond HL.
    do 9 step.
    try rewrite (unsigned_lit 16397105843297379215) by lia.
    rewrite (unsigned_lit (bv_unsigned a0 + -52)) by lia.
    assert (Hx : 0 <= bv_unsigned a0 + -52 < 2^64) by lia.
    rewrite (unsigned_lit (Z.shiftr ((bv_unsigned a0 + -52) * 16397105843297379215) 64)) by (apply shr64_range; exact Hx).
    rewrite (div36_magic _ Hx).
    replace (bv_unsigned a0 + -52) with (bv_unsigned a0 - 52) in * by lia.
    pose proof (Z.div_mod (bv_unsigned a0 - 52) 36 ltac:(lia)) as DM.
    pose proof (Z.mod_pos_bound (bv_unsigned a0 - 52) 36 ltac:(lia)) as MB.
    remember ((bv_unsigned a0 - 52) / 36) as q eqn:Eq.
    rewrite (unsigned_lit q) by lia.
    rewrite (unsigned_lit (q * 36)) by lia.
    if_cases HR.
    + zify_cond HR. try rewrite Z.mod_small in HR by lia.
      assert (U : upstream_result (bv_unsigned a0) = -1).
      { unfold upstream_result, upstream_ok.
        rewrite (proj2 (Z.leb_le 52 (bv_unsigned a0)) ltac:(lia)).
        rewrite (proj2 (Z.eqb_neq ((bv_unsigned a0 - 52) mod 36) 0) ltac:(lia)). reflexivity. }
      step. step. apply evtF_done. rewrite U. do 3 eexists. reflexivity.
    + zify_cond HR.
      do 8 step. apply evtF_done.
      rewrite !(unsigned_lit q) by lia.
      rewrite (sltiu_w q) by lia.
      assert (Ew : upstream_width (bv_unsigned a0) = q mod 2^32) by (unfold upstream_width; rewrite Eq; reflexivity).
      assert (Er : (bv_unsigned a0 - 52) mod 36 = 0) by lia.
      assert (L52 : (52 <=? bv_unsigned a0) = true) by (apply Z.leb_le; lia).
      assert (Hq : 0 <= q < 2^64) by lia.
      unfold upstream_result, upstream_ok. rewrite Ew, Er, L52, even_mod32.
      destruct (2 <=? q mod 2^32) eqn:C1; destruct (q mod 2^32 <=? 40) eqn:C2; destruct (Z.even q) eqn:EV;
        cbn [andb Z.eqb].
      * rewrite (unsigned_lit 0), Z.lor_0_l by lia.
        apply Z.leb_le in C1. apply Z.leb_le in C2.
        rewrite tail_good by (try assumption; lia). do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 0), Z.lor_0_l by lia.
        rewrite (tail_bad q q) by (try lia; rewrite <- Z.negb_even, EV; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
      * rewrite (unsigned_lit 1) by lia.
        rewrite (tail_bad (Z.lor 1 q) q) by (try (apply Z_lor_range; lia); try lia;
          rewrite <- Z.bit0_odd, Z.lor_spec; reflexivity).
        do 3 eexists. reflexivity.
Qed.

(* The old contract from the footprint twin, with the footprint ExecF.RNG_all that holds every access. *)
Theorem reac_upstream_channels_holds_of_F : reac_upstream_channels_contract.
Proof.
  unfold reac_upstream_channels_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m HK.
  pose proof reac_upstream_channels_holds_F as HF. unfold reac_upstream_channels_contract_F in HF.
  apply (ExecF.evtF_evt rsegs ExecF.RNG_all).
  apply HF; [exact HK|].
  apply ExecF.rng_all; unfold UPSTREAM_DIV36_AT; lia.
Qed.
