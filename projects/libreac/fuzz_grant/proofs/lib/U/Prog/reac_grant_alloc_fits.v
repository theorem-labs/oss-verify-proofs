From Stdlib Require Import ZArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantModel reac_grant_alloc_fits_c.
Import ListNotations.
Open Scope Z_scope.

Lemma lxor_sign_mod : forall z, -9223372036854775808 <= z < 9223372036854775808 ->
  Z.lxor (z mod 18446744073709551616) 9223372036854775808 = z + 9223372036854775808.
Proof.
  intros z Hz.
  pose proof (zb_lxor_sign (z mod 18446744073709551616)) as H.
  change (2^63) with 9223372036854775808 in H. change (2^64) with 18446744073709551616 in H.
  rewrite H by (apply Z.mod_pos_bound; lia).
  rewrite Zplus_mod_idemp_l. apply Z.mod_small. lia.
Qed.

Theorem reac_grant_alloc_fits_holds : reac_grant_alloc_fits_contract.
Proof.
  unfold reac_grant_alloc_fits_contract, REAC_GRANT_ALLOC_FITS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m base width -> -> HB HW HS.
  unfold int32 in HB, HW. change (2^31) with 2147483648 in *.
  zstep. zstep. zstep.
  if_cases HC1; zify_cond HC1.
  - assert (Hf : fits base width = false).
    { assert (N : base < 0).
      { destruct (Z_lt_le_dec base 0) as [N|P]; [exact N|]. apply (base_sign base HB) in P. lia. }
      unfold fits. rewrite (proj2 (Z.leb_gt 0 base)) by lia. rewrite andb_false_r. reflexivity. }
    zstep. rewrite Hf. finish.
  - apply (base_sign base HB) in HC1.
    zstep. zstep. zstep.
    if_cases HC2; zify_cond HC2.
    + assert (Hf : fits base width = false).
      { assert (N : ~ (1 <= width <= 40)) by (intros Hw; apply (width_window width HW) in Hw; lia).
        unfold fits. destruct (Z.leb_spec 1 width), (Z.leb_spec width 40); try lia; reflexivity. }
      zstep. rewrite Hf. finish.
    + apply (width_window width HW) in HC2.
      specialize (HS HC1 HC2).
      zstep. zstep. zstep.
      if_cases HC3; zify_cond HC3.
      { exfalso. apply HC3. rewrite swrap32_id by lia. apply Z.mod_small. lia. }
      zstep. zstep. zstep.
      if_cases HC4; zify_cond HC4.
      { exfalso. rewrite ?(Z.mod_small (base + width)) in HC4 by lia.
        rewrite !swrap32_id in HC4 by lia. rewrite !signed64_small in HC4 by lia. lia. }
      zstep. zstep.
      rewrite ?(Z.mod_small (base + width)) by lia.
      rewrite (swrap32_id (base + width + -1)) by lia.
      rewrite (lxor_sign_mod (base + width + -1)) by lia.
      replace (base + width + -1 + 9223372036854775808 <? 9223372036854775856) with (fits base width).
      { finish. }
      unfold fits. rewrite (proj2 (Z.leb_le 1 width)), (proj2 (Z.leb_le width 40)), (proj2 (Z.leb_le 0 base)) by lia.
      cbn [andb]. destruct (Z.leb_spec (base + width) 48); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia.
Qed.
