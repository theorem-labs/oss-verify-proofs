From Stdlib Require Import ZArith List Lia String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import reac_box_family_stem_c.
Import ListNotations.
Open Scope Z_scope.

Lemma STEM_ro : forall f, ro_bytes rsegs (STEM_Addr f) (STEM f).
Proof.
  intros f. unfold STEM_Addr, STEM.
  destruct (f =? 1); [|destruct (f =? 2); [|destruct (f =? 3)]];
  apply ro_bytes_b_sound; vm_compute; reflexivity.
Qed.

Lemma stem_bltu : forall f, -2^31 <= f < 2^31 -> ~ (1 <= f <= 3) ->
  bv_ltu (Z_to_bv 64 2) (Z_to_bv 64 (bv_swrap 32 (bv_unsigned (Z_to_bv 64 f) + -1))) = true.
Proof.
  intros f Hf Hn. rewrite bv_ltu_Z. apply Z.ltb_lt. rewrite !Z_to_bv_unsigned.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64) with 18446744073709551616. change (2 ^ Z.of_N 32) with 4294967296.
  change (4294967296 / 2) with 2147483648.
  Z.div_mod_to_equations. lia.
Qed.

Lemma STEM_Addr_other : forall f, ~ (1 <= f <= 3) -> STEM_Addr f = 0x10533.
Proof.
  intros f Hn. unfold STEM_Addr.
  destruct (Z.eqb_spec f 1); [lia|]. destruct (Z.eqb_spec f 2); [lia|]. destruct (Z.eqb_spec f 3); [lia|].
  reflexivity.
Qed.

Theorem reac_box_family_stem_holds : reac_box_family_stem_contract.
Proof.
  unfold reac_box_family_stem_contract, REAC_BOX_FAMILY_STEM, STEM_T.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m f HF E0 HT.
  subst a0.
  pose proof (STEM_ro f) as RO.
  apply bytes_at_app in HT as [HT1 HT]. rewrite length_le8 in HT.
  apply bytes_at_app in HT as [HT2 HT3]. rewrite length_le8 in HT3.
  assert (C : f = 1 \/ f = 2 \/ f = 3 \/ ~ (1 <= f <= 3)) by lia.
  destruct C as [-> | [-> | [-> | HN]]].
  - assert (RD : ov_read_bytes rsegs m (wa 0x1e3d8) 8 = Some (le8 (Z_to_bv 64 0x102d0))).
    { replace (wa 0x1e3d8) with (wa (0x1e3d8 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m _ _ 0 8 HT1) by (rewrite ?length_le8; lia). reflexivity. }
    step. step. step. if_false. step. step. step. step. step. step.
    apply evt_done. eexists. split; [reflexivity | exact RO].
  - assert (RD : ov_read_bytes rsegs m (wa 0x1e3e0) 8 = Some (le8 (Z_to_bv 64 0x103a4))).
    { replace (wa 0x1e3e0) with (wa (0x1e3d8 + Z.of_nat 8 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m _ _ 0 8 HT2) by (rewrite ?length_le8; lia). reflexivity. }
    step. step. step. if_false. step. step. step. step. step. step.
    apply evt_done. eexists. split; [reflexivity | exact RO].
  - assert (RD : ov_read_bytes rsegs m (wa 0x1e3e8) 8 = Some (le8 (Z_to_bv 64 0x104e9))).
    { replace (wa 0x1e3e8) with (wa (0x1e3d8 + Z.of_nat 8 + Z.of_nat 8 + 0)) by reflexivity.
      rewrite (bytes_at_read rsegs m _ _ 0 8 HT3) by (rewrite ?length_le8; lia). reflexivity. }
    step. step. step. if_false. step. step. step. step. step. step.
    apply evt_done. eexists. split; [reflexivity | exact RO].
  - step. step. step. if_true_by (stem_bltu f HF HN). step. step. step.
    apply evt_done. eexists. split; [rewrite (STEM_Addr_other f HN); reflexivity | exact RO].
Qed.
