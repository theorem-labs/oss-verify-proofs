From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge Step.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_grant.lib.U.Prog Require Import GrantModel reac_grant_allocate_c.
Import ListNotations.
Open Scope Z_scope.

Theorem reac_grant_allocate_holds : reac_grant_allocate_contract.
Proof.
  unfold reac_grant_allocate_contract, REAC_GRANT_ALLOCATE, int32.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m o base w -> -> -> HB HW HS HO.
  change (2^31) with 2147483648 in *.
  assert (Ho : 0 <= o < 2^64) by (destruct HO as [-> | (H1 & H2 & _)]; lia).
  zstep. zstep. zstep.
  if_cases HC1; zify_cond HC1.
  - assert (Hf : fits base w = false).
    { assert (N : base < 0).
      { destruct (Z_lt_le_dec base 0) as [N|P]; [exact N|]. apply (base_sign base HB) in P. lia. }
      unfold fits. rewrite (proj2 (Z.leb_gt 0 base)) by lia. rewrite andb_false_r. reflexivity. }
    zstep. apply evt_done. do 16 eexists. split; [reflexivity|].
    rewrite Hf, andb_false_r. split; reflexivity.
  - apply (base_sign base HB) in HC1.
    zstep.
    if_cases HC2; zify_cond HC2.
    + subst o. zstep. apply evt_done. do 16 eexists. split; [reflexivity|]. cbn. split; reflexivity.
    + destruct HO as [-> | (Hpos & Hend & HWR)]; [lia|].
      zstep. zstep. zstep.
      if_cases HC3; zify_cond HC3.
      * assert (Hf : fits base w = false).
        { assert (N : ~ (1 <= w <= 40)) by (intros Hw; apply (width_window w HW) in Hw; lia).
          unfold fits. destruct (Z.leb_spec 1 w), (Z.leb_spec w 40); try lia; reflexivity. }
        zstep. apply evt_done. do 16 eexists. split; [reflexivity|].
        rewrite Hf, andb_false_r. split; reflexivity.
      * apply (width_window w HW) in HC3.
        specialize (HS HC1 HC3).
        zstep. zstep. zstep.
        if_cases HC4; zify_cond HC4.
        { exfalso. apply HC4. rewrite ?(Z.mod_small w) by lia. rewrite swrap32_id by lia. apply Z.mod_small. lia. }
        zstep. zstep. zstep.
        if_cases HC5; zify_cond HC5.
        { exfalso. rewrite ?(Z.mod_small (base + w)) in HC5 by lia.
          rewrite !swrap32_id in HC5 by lia. rewrite !signed64_small in HC5 by lia. lia. }
        zstep. zstep.
        if_cases HC6; zify_cond HC6;
          rewrite ?(Z.mod_small (base + w)) in HC6 by lia;
          rewrite (swrap32_id (base + w + -1)) in HC6 by lia;
          rewrite signed64_small in HC6 by lia.
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
