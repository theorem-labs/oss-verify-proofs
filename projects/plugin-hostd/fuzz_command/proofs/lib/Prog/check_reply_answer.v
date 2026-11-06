From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel CommandTac strcmp_c sup_reply_code_c strcspn_c strncmp_c check_reply_answer_c.
Import ListNotations.
Open Scope Z_scope.

Lemma neg_mod64 : forall v, -2^63 <= v < 0 -> v mod 18446744073709551616 = v + 18446744073709551616.
Proof. intros v Hv. symmetry. apply Z.mod_unique with (-1); lia. Qed.

Ltac fix_ret :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [lia | reflexivity])
  end.

Ltac after_call MU1 WM1 :=
  lazymatch type of MU1 with munch _ ?mq ?mq' => transport_after_call rsegs mq mq' MU1 WM1 end.

Theorem check_reply_answer_holds :
  strcmp_contract -> sup_reply_code_contract -> strcspn_contract -> strncmp_contract -> check_reply_answer_contract.
Proof.
  intros SC SRC SCS SNC. unfold strcspn_contract in SCS. unfold strncmp_contract in SNC.
  unfold check_reply_answer_contract, CHECK_REPLY_ANSWER, CHECK_REPLY_ANSWER_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  intros ans rep ww p0 xr xa w0 n can.
  intros MI ST LO IE HG HA HR HGG HC RNZ [XRb XRn] XRd XA NR HN HNd HW HWd HS OK.
  unfold void_post.
  apply bytes_ro8 in HG, HA, HR, HW. apply bytes_ro4 in HN.
  unfold outside_stack, disjoint_from in XRd, HNd, HWd.
  unfold GOT_GREC, G_REC, REC_ANSWER, REC_REPLY, GOT_GUARD, GUARD, IMG_END, WORDS_N, WORDS_W in *.
  change (212296 + 912) with 213208 in HA. change (212296 + 928) with 213224 in HR.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 rep) as Rr.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (reply_code_range xr) as RCR.
  assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
  assert (SPR : bv_unsigned sp < 2^64) by (destruct Rsp as [_ Hr]; exact Hr).
  assert (SPv : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16)
    by (apply unsigned_lit; split; [Lia.lia | Lia.lia]).
  destruct (Z.eq_dec (bv_unsigned ans) 0) as [AZ|ANZ].
  - clear XA. destruct OK as [_ OK]. specialize (OK AZ).
    destruct (Z_lt_le_dec (reply_code xr) 0) as [RCn|RCp].
    + clear HS OK HN HNd HW HWd.
      pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
      pose proof (wmono_refl rsegs m) as WM.
      carve_frame 16%nat ST.
      do 7 zstep.
      zstep. if_cases HZ.
      * do 3 zstep.
        pose proof (lit_at _ RESP_LIT resp_lit_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold RESP_LIT; lia)
                      ltac:(unfold RESP_LIT; cbn; lia)) as HL0.
        eapply evt_cut.
        { eapply SRC with (lo := lo) (x := xr).
          - exact MI.
          - rewrite SPv. exact ST.
          - rewrite SPv. unfold SUP_REPLY_CODE_FRAME. lia.
          - exact RNZ.
          - exact XRb.
          - exact XRn.
          - rewrite SPv. unfold SUP_REPLY_CODE_FRAME. lia.
          - exact HL0.
          - rewrite SPv. unfold SUP_REPLY_CODE_FRAME, RESP_LIT. lia. }
        intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mc1 &
                    E & MU1 & WM1 & MI1 & ST1).
        subst ms'. rewrite SPv in MU1, ST1. unfold SUP_REPLY_CODE_FRAME in MU1.
        clear HL0.
        after_call MU1 WM1.
        try clear MI.
        clear MU1 WM1.
        fix_ret.
        zstep. if_cases HB.
        -- do 3 zstep. release_frame FR ST1 (bv_unsigned sp). zstep. finish.
        -- exfalso. zify_cond HB.
           rewrite neg_mod64 in HB by lia. lia.
      * exfalso. zify_cond HZ. lia.
    + destruct OK as [RCn'|[N1 W0]]; [lia|]. subst n.
      destruct (HS eq_refl) as (HP & HPd & [HPb HPn] & HPsd). clear HS.
      apply bytes_ro8 in HP. unfold outside_stack, disjoint_from in HPd, HPsd.
      pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
      pose proof (wmono_refl rsegs m) as WM.
      carve_frame 16%nat ST.
      do 7 zstep.
      zstep. if_cases HZ.
      * do 3 zstep.
        pose proof (lit_at _ RESP_LIT resp_lit_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold RESP_LIT; lia)
                      ltac:(unfold RESP_LIT; cbn; lia)) as HL0.
        eapply evt_cut.
        { eapply SRC with (lo := lo) (x := xr).
          - exact MI.
          - rewrite SPv. exact ST.
          - rewrite SPv. unfold SUP_REPLY_CODE_FRAME. lia.
          - exact RNZ.
          - exact XRb.
          - exact XRn.
          - rewrite SPv. unfold SUP_REPLY_CODE_FRAME. lia.
          - exact HL0.
          - rewrite SPv. unfold SUP_REPLY_CODE_FRAME, RESP_LIT. lia. }
        intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & mc1 &
                    E & MU1 & WM1 & MI1 & ST1).
        subst ms'. rewrite SPv in MU1, ST1. unfold SUP_REPLY_CODE_FRAME in MU1.
        clear HL0.
        after_call MU1 WM1.
        try clear MI.
        clear MU1 WM1.
        fix_ret.
        zstep. if_cases HB.
        -- exfalso. zify_cond HB. lia.
        -- do 3 zstep. if_cases HNE.
           ++ exfalso. vm_compute in HNE. discriminate HNE.
           ++ do 6 zstep.
              pose proof (lit_at _ LIT_SPTAB (str [32; 9] ++ [NUL]) MI1 ltac:(vm_compute; reflexivity)
                            ltac:(unfold LIT_SPTAB; lia) ltac:(unfold LIT_SPTAB; cbn; lia)) as HT.
              eapply evt_cut.
              { eapply SCS with (str := w0) (slack := []) (set := str [32; 9]) (lo := lo) (can := can).
                - exact HPb.
                - exact HPn.
                - intros L. cbn in L. lia.
                - rewrite unsigned_lit by lia. exact HT.
                - apply notin_nul_lit. vm_compute. reflexivity.
                - exact HGG.
                - exact HC.
                - rewrite SPv. exact ST1.
                - rewrite SPv. lia.
                - rewrite SPv. cbn [length Z.of_nat]. lia.
                - rewrite unsigned_lit by lia. left. cbn. lia.
                - unfold CSPN_SSP_GOT. lia.
                - unfold CSPN_SSP_GUARD. lia.
                - exact MI1. }
              intros ms' (t0'' & t1'' & t2'' & a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & a7'' & t3'' & t4'' & t5'' & t6'' & mc2 &
                          E & MU2 & WM2 & MI2 & ST2).
              subst ms'. rewrite SPv in MU2, ST2.
              clear HT.
              after_call MU2 WM2.
              try clear MI1.
              clear MU2 WM2.
              fix_ret.
              replace (Z.of_nat (cspn_len (str [32; 9]) w0)) with 4 by (rewrite W0; vm_compute; reflexivity).
              do 2 zstep. if_cases HNE4.
              ** exfalso. vm_compute in HNE4. discriminate HNE4.
              ** do 5 zstep.
                 pose proof (lit_at _ LIT_QUIT (S_QUIT ++ [NUL]) MI2 ltac:(vm_compute; reflexivity)
                               ltac:(unfold LIT_QUIT; lia) ltac:(unfold LIT_QUIT; cbn; lia)) as HQ.
                 eapply evt_cut.
                 { eapply SNC with (ls := w0 ++ [NUL]) (rs := S_QUIT ++ [NUL]) (v := 0).
                   - exact HPb.
                   - rewrite unsigned_lit by lia. exact HQ.
                   - rewrite W0. vm_compute. reflexivity.
                   - exact MI2. }
                 intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & mc3 &
                             E & MU3 & WM3 & MI3 & HB1 & HB2).
                 subst ms'. clear HB1 HB2 HQ.
                 after_call MU3 WM3.
                 try clear MI2.
                 clear MU3 WM3.
                 fix_ret.
                 zstep. if_cases HZ0.
                 --- exfalso. vm_compute in HZ0. discriminate HZ0.
                 --- do 3 zstep. release_frame FR ST2 (bv_unsigned sp). zstep. finish.
      * exfalso. zify_cond HZ. lia.
  - destruct (XA ANZ) as [[XAb XAn] XAd]. clear XA HS HN HNd HW HWd.
    destruct OK as [OK _]. specialize (OK ANZ).
    unfold outside_stack, disjoint_from in XAd.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 16%nat ST.
    do 7 zstep.
    zstep. if_cases HZ.
    + exfalso. zify_cond HZ. lia.
    + zstep. zstep.
      eapply evt_cut.
      { eapply SC with (sx := xr) (sy := xa).
        - exact XRb.
        - exact XRn.
        - exact XAb.
        - exact XAn. }
      intros ms' (rr & x11 & x12 & x13 & E & Hrr). subst ms'.
      fix_ret.
      assert (RR0 : rr = Z_to_bv 64 0) by (apply Hrr; exact OK).
      subst rr.
      zstep. if_cases HZ0.
      * do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
      * exfalso. vm_compute in HZ0. discriminate HZ0.
Qed.
