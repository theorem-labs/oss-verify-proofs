From Stdlib Require Import ZArith List Lia Bool Znumtheory.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel reac_grant_alloc_fits_c.
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

Lemma fits_code : forall base width, int32 base -> int32 width ->
  (0 <= base -> 1 <= width <= 40 -> base + width < 2^31) ->
  Z.land
    (Z.land
       (Z.lxor (Z.b2z (Z.lxor (base mod 18446744073709551616) 9223372036854775808 <? 9223372036854775808))
          18446744073709551615)
       (Z.b2z (bv_swrap 32 (width mod 18446744073709551616 + -1) mod 18446744073709551616 <? 40)))
    (Z.b2z (Z.lxor (bv_swrap 32 (width mod 18446744073709551616 + base mod 18446744073709551616)
                       mod 18446744073709551616) 9223372036854775808 <? 9223372036854775857))
  = Z.b2z (fits base width).
Proof.
  unfold int32. intros base width HB HW HS.
  change (2^31) with 2147483648 in *.
  rewrite (lxor_sign_mod base) by lia.
  rewrite (swrap32_mod64 width (-1)).
  assert (E2 : (bv_swrap 32 (width + -1) mod 18446744073709551616 <? 40) = (1 <=? width) && (width <=? 40)).
  { destruct (Z.eq_dec width (-2147483648)) as [E|NE].
    - subst width. reflexivity.
    - rewrite swrap32_id by lia.
      destruct (Z_lt_le_dec width 1).
      + rewrite <- (Z.mod_add (width + -1) 1 18446744073709551616) by lia. rewrite Z.mod_small by lia.
        rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.leb_gt 1 width)) by lia. reflexivity.
      + rewrite Z.mod_small by lia. rewrite (proj2 (Z.leb_le 1 width)) by lia. cbn [andb].
        destruct (Z.leb_spec width 40); [apply Z.ltb_lt | apply Z.ltb_ge]; lia. }
  rewrite E2. unfold fits.
  replace (base + 9223372036854775808 <? 9223372036854775808) with (negb (0 <=? base))
    by (destruct (Z.leb_spec 0 base); symmetry; [apply Z.ltb_ge | apply Z.ltb_lt]; lia).
  destruct (Z.leb_spec 0 base) as [H0|H0]; [destruct (Z.leb_spec 1 width) as [H1|H1]; [destruct (Z.leb_spec width 40) as [H2|H2]|]|].
  - rewrite (swrap32_mod64 width (base mod 18446744073709551616)).
    rewrite (Z.add_comm width (base mod 18446744073709551616)), (swrap32_mod64 base width).
    rewrite (swrap32_id (base + width)) by (specialize (HS H0 (conj H1 H2)); lia).
    rewrite (lxor_sign_mod (base + width)) by (specialize (HS H0 (conj H1 H2)); lia).
    replace (base + width + 9223372036854775808 <? 9223372036854775857) with (base + width <=? 48)
      by (destruct (Z.leb_spec (base + width) 48); symmetry; [apply Z.ltb_lt | apply Z.ltb_ge]; lia).
    destruct (base + width <=? 48); reflexivity.
  - repeat match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) end; reflexivity.
  - repeat match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) end; reflexivity.
  - repeat match goal with |- context [Z.ltb ?x ?y] => destruct (Z.ltb x y) | |- context [Z.leb ?x ?y] => destruct (Z.leb x y) end; reflexivity.
Qed.

Theorem reac_grant_alloc_fits_holds : reac_grant_alloc_fits_contract.
Proof.
  unfold reac_grant_alloc_fits_contract, REAC_GRANT_ALLOC_FITS.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m base width -> -> HB HW HS.
  zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  rewrite fits_code by assumption.
  finish.
Qed.
