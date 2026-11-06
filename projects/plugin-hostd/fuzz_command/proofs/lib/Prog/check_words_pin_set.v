From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel CommandTac strncmp_c strcmp_c check_words_pin_set_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_words_pin_set_holds : strncmp_contract -> strcmp_contract -> check_words_pin_set_contract.
Proof.
  intros SNC SC. unfold strncmp_contract in SNC. unfold check_words_pin_set_contract, CHECK_WORDS_PIN_SET, CHECK_WORDS_PIN_SET_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  intros r nargs p4 p3 w4 x3.
  intros MI ST LO IE RR HA2 HW4 RN HN HND HW3 N4 X3.
  subst a2 nargs.
  destruct (HW3 eq_refl) as (H3s & H3d & [H3b H3n] & H3sd). clear HW3.
  unfold void_post, outside_stack, disjoint_from, CALL_NARGS, CALL_ARGS, IMG_END in *.
  apply bytes_ro4 in HN. apply bytes_ro8 in H3s.
  replace (bv_unsigned a0 + 8 + 24) with (bv_unsigned a0 + 32) in * by lia.
  assert (SGr : bv_signed (Z_to_bv 64 r) = r).
  { rewrite zb_signed, unsigned_lit by lia. destruct (Z.ltb_spec r (2^63)); lia. }
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
  destruct (Z_le_gt_dec r 4) as [Rle|Rgt].
  - clear HW4.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    do 6 zstep.
    zstep. if_cases HR.
    + zify_cond HR. rewrite SGr in HR.
      do 5 zstep. if_cases HNE.
      * exfalso. vm_compute in HNE. discriminate HNE.
      * zstep. zstep.
        pose proof (lit_at _ LIT_DASH (S_DASH ++ [NUL]) MI ltac:(vm_compute; reflexivity) ltac:(unfold LIT_DASH; lia)
                      ltac:(unfold LIT_DASH; cbn; lia)) as HD.
        assert (XD : x3 = S_DASH) by (rewrite X3; unfold pin_verdict; rewrite (proj2 (Z.leb_le r 4)) by lia; reflexivity).
        eapply evt_cut.
        { eapply SC with (sx := x3) (sy := S_DASH).
          - exact H3b.
          - exact H3n.
          - replace (bv_unsigned (Z_to_bv 64 67760)) with LIT_DASH by reflexivity. exact HD.
          - apply notin_nul_lit. vm_compute. reflexivity. }
        intros ms' (rr & x11 & x12 & x13 & E & Hrr). subst ms'.
        replace (ret_pc (Z_to_bv 64 86976)) with (Z_to_bv 64 86976) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        assert (RR0 : rr = Z_to_bv 64 0) by (apply Hrr; exact XD).
        subst rr.
        zstep. if_cases HZ.
        -- exfalso. vm_compute in HZ. discriminate HZ.
        -- do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
    + exfalso. zify_cond HR. rewrite SGr in HR. lia.
  - destruct (HW4 ltac:(lia)) as (H4s & H4d & [H4b H4n] & H4sd). clear HW4.
    apply bytes_ro8 in H4s. unfold outside_stack, disjoint_from in H4d, H4sd.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    do 6 zstep.
    zstep. if_cases HR.
    + exfalso. zify_cond HR. rewrite SGr in HR. lia.
    + zify_cond HR. rewrite SGr in HR.
      do 6 zstep.
      pose proof (lit_at _ LIT_VERDICT (S_VERDICT ++ [NUL]) MI ltac:(vm_compute; reflexivity) ltac:(unfold LIT_VERDICT; lia)
                    ltac:(unfold LIT_VERDICT; cbn; lia)) as HK.
      destruct (strncmp_prefix w4 S_VERDICT H4n ltac:(apply notin_nul_lit; vm_compute; reflexivity) ltac:(discriminate))
        as (v & Hv & Hv0).
      eapply evt_cut.
      { eapply SNC with (ls := w4 ++ [NUL]) (rs := S_VERDICT ++ [NUL]) (v := v).
        - exact H4b.
        - replace (bv_unsigned (Z_to_bv 64 67531)) with LIT_VERDICT by reflexivity. exact HK.
        - replace (bv_unsigned (Z_to_bv 64 8)) with (Z.of_nat (length S_VERDICT)) by reflexivity. exact Hv.
        - exact MI. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                  E & MU1 & WM1 & MI1 & HB1 & HB2).
      subst ms'. clear HB1 HB2 HK.
      transport_after_call rsegs m0 m1 MU1 WM1.
      clear MU1 WM1 MI.
      replace (ret_pc (Z_to_bv 64 86932)) with (Z_to_bv 64 86932) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      do 3 zstep.
      pose proof (strncmp_model_range _ _ _ _ Hv) as VR.
      pose proof (proj1 H4b) as P4lo. pose proof (proj1 (proj2 H4b)) as P4hi.
      rewrite length_app in P4hi. cbn [length] in P4hi.
      pose proof (lit_at _ LIT_DASH (S_DASH ++ [NUL]) MI1 ltac:(vm_compute; reflexivity) ltac:(unfold LIT_DASH; lia)
                    ltac:(unfold LIT_DASH; cbn; lia)) as HD.
      destruct (Z.eq_dec v 0) as [V0|VN].
      * subst v. rewrite sel8_zero.
        assert (PF : firstn (length S_VERDICT) w4 = S_VERDICT) by (apply Hv0; reflexivity).
        assert (L8 : (8 <= length w4)%nat).
        { pose proof (f_equal (@length byte) PF) as L. rewrite firstn_length in L. change (length S_VERDICT) with 8%nat in L. lia. }
        assert (XV : x3 = skipn 8 w4).
        { rewrite X3. unfold pin_verdict. rewrite (proj2 (Z.leb_gt r 4)) by lia.
          rewrite (proj2 (prefixb_iff w4 S_VERDICT) PF). reflexivity. }
        pose proof (bytes_at_skipn _ _ _ 8 H4b ltac:(rewrite length_app; cbn; lia)) as H8.
        rewrite skipn_cstr in H8 by exact L8.
        do 4 zstep. if_cases HNE.
        -- exfalso. vm_compute in HNE. discriminate HNE.
        -- zstep. zstep.
           eapply evt_cut.
           { eapply SC with (sx := x3) (sy := skipn 8 w4).
             - exact H3b.
             - exact H3n.
             - rewrite unsigned_lit by lia. exact H8.
             - apply notin_skipn. exact H4n. }
           intros ms' (rr & x11 & x12 & x13 & E & Hrr). subst ms'.
           replace (ret_pc (Z_to_bv 64 86976)) with (Z_to_bv 64 86976) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
           assert (RR0 : rr = Z_to_bv 64 0) by (apply Hrr; exact XV).
           subst rr.
           zstep. if_cases HZ.
           ++ exfalso. vm_compute in HZ. discriminate HZ.
           ++ do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
      * rewrite (sel8_nonzero v VN VR), Z_to_bv_plus0.
        assert (NPF : firstn (length S_VERDICT) w4 <> S_VERDICT) by (intros H; apply VN, Hv0, H).
        assert (XV : x3 = w4).
        { rewrite X3. unfold pin_verdict. rewrite (proj2 (Z.leb_gt r 4)) by lia.
          destruct (prefixb w4 S_VERDICT) eqn:PB; [exfalso; apply NPF, prefixb_iff, PB | reflexivity]. }
        do 4 zstep. if_cases HNE.
        -- exfalso. vm_compute in HNE. discriminate HNE.
        -- zstep. zstep.
           eapply evt_cut.
           { eapply SC with (sx := x3) (sy := w4).
             - exact H3b.
             - exact H3n.
             - exact H4b.
             - exact H4n. }
           intros ms' (rr & x11 & x12 & x13 & E & Hrr). subst ms'.
           replace (ret_pc (Z_to_bv 64 86976)) with (Z_to_bv 64 86976) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
           assert (RR0 : rr = Z_to_bv 64 0) by (apply Hrr; exact XV).
           subst rr.
           zstep. if_cases HZ.
           ++ exfalso. vm_compute in HZ. discriminate HZ.
           ++ do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
Qed.
