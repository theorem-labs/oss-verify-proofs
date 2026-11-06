From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import strlen_c bcmp_c has_prefix_c.
Import ListNotations.
Open Scope Z_scope.

Lemma has_prefix_memcmp : forall n (L R : list byte) v, length L = n -> length R = n -> memcmp_model L R n = Some v ->
  -255 <= v <= 255 /\ (v = 0 <-> L = R).
Proof.
  induction n as [|n IH]; intros L R v HL HR HM.
  - destruct L, R; cbn in *; try lia. injection HM as <-. split; [lia|]. tauto.
  - destruct L as [|a L], R as [|b R]; cbn in HL, HR; try lia.
    cbn in HM. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + destruct (IH L R v ltac:(lia) ltac:(lia) HM) as [RV IV]. split; [exact RV|].
      rewrite IV. split; intro H.
      * f_equal; [apply bv_eq; exact E | exact H].
      * injection H as _ H. exact H.
    + injection HM as <-. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
      unfold bv_modulus in Ra, Rb. change (Z.of_N 8) with 8 in Ra, Rb.
      split; [lia|]. split; intro H; [lia|]. injection H as H _. subst. contradiction.
Qed.

Theorem has_prefix_holds : strlen_contract -> bcmp_contract -> has_prefix_contract.
Proof.
  intros HSL HBC. unfold has_prefix_contract, HAS_PREFIX, HAS_PREFIX_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    S P slack HS HN HP PNZ PSL MI ST LO DS DP.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word a0) as Ra0. pose proof (zr_word a1) as Ra1.
  pose proof (zr_word a2) as Ra2. unfold inr64 in *.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (bytes_at_bound _ _ _ _ HP) as BP. rewrite length_app in BP. cbn [length] in BP.
  pose proof (bytes_at_bound _ _ _ _ HS) as BS.
  carve_frame 32%nat ST.
  do 10 zstep.
  eapply evt_cut.
  { eapply HSL with (str := P) (slack := slack); [exact HP | exact PNZ | exact PSL | exact MI]. }
  post_call rsegs m1.
  zstep.
  if_cases HB.
  - try unfold c_ltu in HB. zify_cond HB.
    do 4 zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mc end.
    assert (FS : bytes_at rsegs mc (bv_unsigned a0) (firstn (length P) S)).
    { apply (proj1 (proj1 (bytes_at_app rsegs mc (bv_unsigned a0) (firstn (length P) S) (skipn (length P) S))
                     ltac:(rewrite firstn_skipn; exact HS))). }
    assert (FP : bytes_at rsegs mc (bv_unsigned a2) P).
    { exact (proj1 (proj1 (bytes_at_app rsegs mc (bv_unsigned a2) P (Z_to_bv 8 0 :: slack)) HP)). }
    destruct (memcmp_model_total (firstn (length P) S) P (length P) ltac:(rewrite firstn_length; lia) ltac:(lia))
      as [v HMv].
    destruct (has_prefix_memcmp (length P) (firstn (length P) S) P v ltac:(rewrite firstn_length; lia) eq_refl HMv)
      as [RV IV].
    eapply evt_cut.
    { eapply HBC with (ls := firstn (length P) S) (rs := P) (v := v); [exact FS | exact FP | | eassumption].
      rewrite unsigned_lit by lia. rewrite Nat2Z.id. exact HMv. }
    post_call rsegs mc.
    zstep. do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
    unfold prefix_of. destruct (Z.eq_dec v 0) as [V0|V0].
    + subst v. left. split; [|reflexivity]. split; [lia|]. apply IV. reflexivity.
    + right. split.
      * intros [_ E]. apply V0. apply IV. exact E.
      * match goal with |- context [Z.ltb ?x 1] =>
          replace (Z.ltb x 1) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia) end.
        reflexivity.
  - try unfold c_ltu in HB. zify_cond HB.
    do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
    unfold prefix_of. right. split; [|reflexivity]. intros [Hl _]. lia.
Qed.
