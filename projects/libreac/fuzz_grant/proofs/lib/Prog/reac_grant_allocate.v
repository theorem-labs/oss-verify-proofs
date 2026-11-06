From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Prog Require Import GrantModel reac_grant_allocate_c.
Import ListNotations.
Open Scope Z_scope.

Lemma inrange_code : forall w, -2147483648 <= w < 2147483648 ->
  (bv_swrap 32 (w mod 18446744073709551616 + -41) mod 18446744073709551616 <? 18446744073709551576)
  = negb ((1 <=? w) && (w <=? 40)).
Proof.
  intros w Hw. rewrite swrap32_mod64.
  destruct (Z_lt_le_dec (w + -41) (-2147483648)) as [L|L].
  - assert (E : bv_swrap 32 (w + -41) = w + -41 + 4294967296).
    { unfold bv_swrap, bv_wrap. change (bv_modulus 32) with 4294967296. change (bv_half_modulus 32) with 2147483648.
      rewrite <- (Z.mod_add (w + -41 + 2147483648) 1 4294967296) by lia. rewrite Z.mod_small by lia. lia. }
    rewrite E, Z.mod_small by lia.
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.leb_gt 1 w)) by lia. reflexivity.
  - rewrite swrap32_id by lia.
    destruct (Z_lt_le_dec w 1) as [L1|L1].
    + rewrite <- (Z.mod_add (w + -41) 1 18446744073709551616) by lia. rewrite Z.mod_small by lia.
      rewrite (proj2 (Z.ltb_lt _ _)) by lia. rewrite (proj2 (Z.leb_gt 1 w)) by lia. reflexivity.
    + rewrite (proj2 (Z.leb_le 1 w)) by lia. cbn [andb].
      destruct (Z_lt_le_dec 40 w) as [L2|L2].
      * rewrite Z.mod_small by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia.
        rewrite (proj2 (Z.leb_gt w 40)) by lia. reflexivity.
      * rewrite <- (Z.mod_add (w + -41) 1 18446744073709551616) by lia. rewrite Z.mod_small by lia.
        rewrite (proj2 (Z.ltb_ge _ _)) by lia. rewrite (proj2 (Z.leb_le w 40)) by lia. reflexivity.
Qed.

Theorem reac_grant_allocate_holds : reac_grant_allocate_contract.
Proof.
  unfold reac_grant_allocate_contract, REAC_GRANT_ALLOCATE, int32.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o base w -> -> -> HB HW HS HO.
  change (2^31) with 2147483648 in *.
  assert (Ho : 0 <= o < 2^64) by (destruct HO as [-> | (H1 & H2 & _)]; lia).
  zstep. zstep. zstep.
  if_cases HC1; zify_cond HC1.
  - subst o. zstep. apply evt_done. do 16 eexists. split; [reflexivity|]. cbn. split; reflexivity.
  - destruct HO as [-> | (Hpos & Hend & HWR)]; [lia|].
    zstep. zstep. zstep.
    if_cases HC2; zify_cond HC2.
    + assert (E : negb ((1 <=? w) && (w <=? 40)) = true)
        by (rewrite <- inrange_code by lia; apply Z.ltb_lt; exact HC2).
      zstep. apply evt_done. do 16 eexists. split; [reflexivity|].
      replace (negb (o =? 0) && fits base w) with false.
      * split; reflexivity.
      * unfold fits. destruct ((1 <=? w) && (w <=? 40)); [discriminate|]. rewrite andb_false_r. reflexivity.
    + assert (E : negb ((1 <=? w) && (w <=? 40)) = false)
        by (rewrite <- inrange_code by lia; apply Z.ltb_ge; exact HC2).
      assert (Hw1 : 1 <= w <= 40).
      { destruct (Z.leb_spec 1 w), (Z.leb_spec w 40); cbn in E; try discriminate; lia. }
      zstep.
      if_cases HC3; zify_cond HC3.
      * zstep. apply evt_done. do 16 eexists. split; [reflexivity|].
        replace (negb (o =? 0) && fits base w) with false.
        -- split; reflexivity.
        -- unfold fits. rewrite (proj2 (Z.leb_gt 0 base))
             by (destruct (Z_lt_le_dec base 0); [lia | rewrite Z.mod_small in HC3 by lia; lia]).
           rewrite andb_false_r. rewrite andb_false_l. rewrite andb_false_r. reflexivity.
      * assert (Hb0 : 0 <= base).
        { destruct (Z_lt_le_dec base 0); [|lia].
          rewrite <- (Z.mod_add base 1 18446744073709551616) in HC3 by lia. rewrite Z.mod_small in HC3 by lia. lia. }
        zstep. zstep. zstep.
        if_cases HC4; zify_cond HC4;
          idtac;
          try rewrite (swrap32_mod64 w base) in HC4;
          rewrite (swrap32_id (w + base)) in HC4 by (specialize (HS Hb0 Hw1); lia);
          rewrite signed64_small in HC4 by (specialize (HS Hb0 Hw1); lia).
        -- zstep. apply evt_done. do 16 eexists. split; [reflexivity|].
           replace (negb (o =? 0) && fits base w) with false.
           ++ split; reflexivity.
           ++ unfold fits. rewrite (proj2 (Z.leb_gt (base + w) 48)) by lia.
              rewrite !andb_false_r. reflexivity.
        -- zstep.
           assert (HS1 : store_ok rsegs m (wa (o + 0)) 1 = true)
             by (apply (wr_at_store_ok rsegs m o 2 0 1 HWR); lia).
           zstep.
           set (m1 := write_to_mem m (wa (o + 0)) (le1 (Z_to_bv 64 base))).
           assert (HW1 : wr_at rsegs m1 o 2) by (apply wr_at_write; exact HWR).
           assert (HS2 : store_ok rsegs m1 (wa (o + 1)) 1 = true)
             by (apply (wr_at_store_ok rsegs m1 o 2 1 1 HW1); lia).
           zstep.
           match goal with |- context [write_to_mem m1 (Z_to_bv 64 (o + 1)) _] =>
             change (Z_to_bv 64 (o + 1)) with (wa (o + 1)) | _ => idtac end.
           zstep.
           apply evt_done. do 15 eexists. eexists. split; [reflexivity|].
           replace (negb (o =? 0) && fits base w) with true.
           2:{ unfold fits. rewrite (proj2 (Z.eqb_neq o 0)) by lia. rewrite (proj2 (Z.leb_le 1 w)) by lia.
               rewrite (proj2 (Z.leb_le w 40)) by lia. rewrite (proj2 (Z.leb_le 0 base)) by lia.
               rewrite (proj2 (Z.leb_le (base + w) 48)) by lia. reflexivity. }
           split; [reflexivity|]. split; [|split].
           ++ apply bytes_at_app. split.
              ** apply bytes_at_write_other.
                 --- unfold m1. replace (wa (o + 0)) with (wa o) by (f_equal; lia).
                     apply bytes_at_write_same; rewrite ?length_le1; lia.
                 --- lia.
                 --- rewrite length_le1; lia.
                 --- rewrite !length_le1; lia.
              ** rewrite length_le1. change (o + Z.of_nat 1) with (o + 1).
                 apply bytes_at_write_same; rewrite ?length_le1; lia.
           ++ apply munch_write; [ | lia | rewrite length_le1; lia | cbn [inside]; rewrite length_le1; lia ].
              apply munch_write; [ apply munch_refl | lia | rewrite length_le1; lia | cbn [inside]; rewrite length_le1; lia ].
           ++ apply wmono_write. apply wmono_write. apply wmono_refl.
Qed.
