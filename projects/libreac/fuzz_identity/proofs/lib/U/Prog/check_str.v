From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.U.Prog Require Import strlen_c check_str_c.
Import ListNotations.
Open Scope Z_scope.

Lemma check_str_lts_neg : forall r, -2^31 <= r < 0 -> bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = true.
Proof.
  intros r Hr. rewrite bv_lts_zero_r, unsigned_lit_wrap. apply Z.leb_le. Z.div_mod_to_equations. lia.
Qed.

Lemma check_str_lts_pos : forall r, 0 <= r < 2^31 -> bv_lts (Z_to_bv 64 r) (Z_to_bv 64 0) = false.
Proof.
  intros r Hr. rewrite bv_lts_zero_r, unsigned_lit_wrap. apply Z.leb_gt. Z.div_mod_to_equations. lia.
Qed.

Lemma check_str_nul_at : forall (str slack : list byte) b, firstn 1 (skipn (length str) (str ++ b :: slack)) = [b].
Proof. intros. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.

Lemma check_str_ltu : forall r c, 0 <= r -> r < c < 2^64 -> negb (bv_ltu (Z_to_bv 64 r) (Z_to_bv 64 c)) = false.
Proof. intros r c Hr Hc. unfold bv_ltu. rewrite !unsigned_lit by lia. destruct (Z.ltb_spec r c); [reflexivity | lia]. Qed.

Theorem check_str_holds : strlen_contract -> check_str_contract.
Proof.
  intros SL. unfold check_str_contract, CHECK_STR, CHECK_STR_FRAME.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m r o c lo str slack
    HR E0 HO E1 HC E2 OK ST LO MI.
  subst a0 a1 a2.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. change (2 ^ Z.of_N 64) with (2^64) in Rsp.
  destruct (Z_lt_le_dec r 0) as [NEG | POS].
  - clear OK. carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep.
    if_true_by (check_str_lts_neg r ltac:(lia)).
    zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp). zstep. finish.
  - unfold check_str_ok, CHECK_STR_FRAME in OK.
    destruct (OK POS) as (RC & LEN & HB & NZ & WP & DJ). clear OK.
    pose proof (bytes_at_bound rsegs m o _ HB) as HBB. rewrite length_app in HBB. cbn [length] in HBB.
    carve_frame 16%nat ST.
    zstep. zstep. zstep. zstep.
    if_false_by (check_str_lts_pos r ltac:(lia)).
    zstep. zstep.
    if_false_by (check_str_ltu r c ltac:(lia) ltac:(lia)).
    zstep. zstep.
    if_cases HT; zify_cond HT.
    { exfalso.
      first [ solve [ rewrite ?unsigned_lit_wrap, ?zb_lxor_ones in HT by lia; Z.div_mod_to_equations; lia ]
            | match type of HT with ?T => fail 100 "HT:" T end ]. }
    match goal with HB' : bytes_at rsegs ?mm o _ |- _ =>
      assert (RD : ov_read_bytes rsegs mm (wa (o + r)) 1 = Some [Z_to_bv 8 0]) by
        (rewrite (bytes_at_read rsegs mm o _ r 1 HB') by (rewrite ?length_app; cbn [length]; lia);
         replace (Z.to_nat r) with (length str) by lia; rewrite check_str_nul_at; reflexivity) end.
    zstep. zstep. zstep.
    if_false.
    zstep. zstep.
    match goal with HB' : bytes_at rsegs ?mm o _ |- _ =>
      assert (HBo : bytes_at rsegs mm (bv_unsigned (Z_to_bv 64 o)) (str ++ Z_to_bv 8 0 :: slack))
        by (rewrite unsigned_lit by lia; exact HB');
      eapply evt_cut;
      [ eapply SL; [ exact HBo | exact NZ | rewrite unsigned_lit by lia; rewrite LEN; exact WP | assumption ]
      | post_call rsegs mm ]
    end.
    rewrite LEN.
    zstep.
    if_false.
    zstep. zstep. zstep.
    release_frame FR ST (bv_unsigned sp). zstep. finish.
Qed.
