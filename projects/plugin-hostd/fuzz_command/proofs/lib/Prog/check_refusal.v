From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Prog Require Import CommandModel CommandTac sup_reply_code_c check_refusal_c.
Import ListNotations.
Open Scope Z_scope.

Theorem check_refusal_holds : sup_reply_code_contract -> check_refusal_contract.
Proof.
  intros SRC. unfold check_refusal_contract, CHECK_REFUSAL, CHECK_REFUSAL_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo.
  intros reply state quit x.
  intros MI ST LO IE HG HR HS HGQ RQ HQ HX OK.
  unfold void_post.
  apply bytes_ro8 in HG, HR, HS, HGQ. apply bytes_ro4 in HQ.
  unfold GOT_GREC, G_REC, REC_REPLY, REC_STATE, GOT_GQUIT, G_QUIT, IMG_END in *.
  change (212296 + 928) with 213224 in HR. change (212296 + 944) with 213240 in HS.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 reply) as Rr.
  pose proof (lit_at m RESP_LIT resp_lit_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold RESP_LIT; lia)
                ltac:(unfold RESP_LIT; cbn; lia)) as HL.
  destruct (Z.eq_dec (bv_unsigned reply) 0) as [RZ|RNZ].
  - clear HX OK.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    do 7 zstep.
    zstep. if_cases HZ.
    + do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
    + exfalso. zify_cond HZ. lia.
  - destruct (HX RNZ) as [[HXb HXn] HXd]. specialize (OK RNZ). clear HX.
    unfold outside_stack, disjoint_from in HXd.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    carve_frame 32%nat ST.
    do 7 zstep.
    zstep. if_cases HZ.
    + exfalso. zify_cond HZ. lia.
    + do 3 zstep.
      assert (LO0 : 0 <= lo) by (destruct ST as [Hl _]; exact Hl).
      assert (SPR : bv_unsigned sp < 2^64) by (destruct Rsp as [_ Hr]; exact Hr).
      assert (SPv : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32)
        by (apply unsigned_lit; split; [Lia.lia | Lia.lia]).
      pose proof (lit_at _ RESP_LIT resp_lit_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold RESP_LIT; lia)
                    ltac:(unfold RESP_LIT; cbn; lia)) as HL0.
      eapply evt_cut.
      { eapply SRC with (lo := lo) (x := x).
        - exact MI.
        - rewrite SPv. exact ST.
        - rewrite SPv. unfold SUP_REPLY_CODE_FRAME. lia.
        - exact RNZ.
        - exact HXb.
        - exact HXn.
        - rewrite SPv. unfold SUP_REPLY_CODE_FRAME. lia.
        - exact HL0.
        - rewrite SPv. unfold SUP_REPLY_CODE_FRAME, RESP_LIT. lia. }
      intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m1 &
                  E & MU1 & WM1 & MI1 & ST1).
      subst ms'. rewrite SPv in MU1, ST1. unfold SUP_REPLY_CODE_FRAME in MU1.
      clear HL0.
      transport_after_call rsegs m0 m1 MU1 WM1.
      try clear MI.
      clear MU1 WM1.
      replace (ret_pc (Z_to_bv 64 85060)) with (Z_to_bv 64 85060) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      pose proof (reply_code_range x) as RC.
      zstep. if_cases HB.
      * do 4 zstep. release_frame FR ST1 (bv_unsigned sp). zstep. finish.
      * zify_cond HB.
        assert (RCn : reply_code x < 0).
        { destruct (Z_lt_le_dec (reply_code x) 0) as [Hn|Hge]; [exact Hn|].
          rewrite Z.mod_small in HB by lia. lia. }
        destruct (OK RCn) as [ES EQ]. subst state quit.
        zstep. zstep. if_cases HE.
        -- exfalso. zify_cond HE. lia.
        -- do 4 zstep. if_cases HQ0.
           ++ exfalso. vm_compute in HQ0. discriminate HQ0.
           ++ do 4 zstep. release_frame FR ST1 (bv_unsigned sp). zstep. finish.
Qed.
