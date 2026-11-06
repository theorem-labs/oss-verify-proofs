From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import strlen_c bcmp_c jtok_is_c.
Import ListNotations.
Open Scope Z_scope.

Lemma jtok_is_sx32 : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with (2^31). change (bv_modulus 32) with (2^32).
  Z.div_mod_to_equations. lia.
Qed.

Lemma jtok_is_eqb : forall x y, -2^31 <= x < 2^31 -> -2^31 <= y < 2^31 ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold bv_eqb. rewrite !unsigned_lit_wrap.
  destruct (Z.eqb_spec x y) as [->|NE]; [apply Z.eqb_refl|]. apply Z.eqb_neq. intro E. apply NE.
  Z.div_mod_to_equations. lia.
Qed.

Lemma jtok_is_eqb_u : forall (x : word) y, 0 <= y < 2^64 -> bv_eqb x (Z_to_bv 64 y) = (bv_unsigned x =? y).
Proof. intros x y Hy. unfold bv_eqb. rewrite unsigned_lit by lia. reflexivity. Qed.

Lemma jtok_is_memcmp : forall n (P T : list byte) v, length P = n -> length T = n -> memcmp_model P T n = Some v ->
  -255 <= v <= 255 /\ (v = 0 <-> P = T).
Proof.
  induction n as [|n IH]; intros P T v HP HT HM.
  - destruct P, T; cbn in *; try lia. injection HM as <-. split; [lia|]. tauto.
  - destruct P as [|a P], T as [|b T]; cbn in HP, HT; try lia.
    cbn in HM. destruct (Z.eqb_spec (bv_unsigned a) (bv_unsigned b)) as [E|NE].
    + destruct (IH P T v ltac:(lia) ltac:(lia) HM) as [R I]. split; [exact R|].
      rewrite I. split; intro H.
      * f_equal; [apply bv_eq; exact E | exact H].
      * injection H as _ H. exact H.
    + injection HM as <-. pose proof (bv_unsigned_in_range 8 a) as Ra. pose proof (bv_unsigned_in_range 8 b) as Rb.
      unfold bv_modulus in Ra, Rb. change (Z.of_N 8) with 8 in Ra, Rb.
      split; [lia|]. split; intro H; [lia|]. injection H as H _. subst. contradiction.
Qed.

Theorem jtok_is_holds : strlen_contract -> bcmp_contract -> jtok_is_contract.
Proof.
  intros STRLEN BCMP. unfold jtok_is_contract, JTOK_IS, JTOK_IS_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    kind vk vp vn T slack P HK HA1 HVK HV HT TNZ TSL HP MI ST LO DV DT.
  subst a1.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  pose proof (zr_word sp) as Rsp. pose proof (zr_word a0) as Ra0. pose proof (zr_word a2) as Ra2.
  pose proof (zr_word vp) as Rvp. pose proof (zr_word vn) as Rvn. unfold inr64 in *.
  assert (L0 : 0 <= lo) by (destruct ST as [? _]; lia).
  pose proof (bytes_at_bound _ _ _ _ HT) as BT. rewrite length_app in BT. cbn [length] in BT.
  assert (RV : ro_cells rsegs m (bv_unsigned a0) [C8 vp; C8 vn; C4 (Z_to_bv 64 vk)]).
  { split; [cbn; tauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact HV. }
  clear HV.
  carve_frame 32%nat ST.
  do 10 zstep.
  eapply evt_cut.
  { eapply STRLEN with (str := T) (slack := slack); [exact HT | exact TNZ | exact TSL | exact MI]. }
  post_call rsegs m1.
  zstep.
  rewrite jtok_is_sx32 by lia.
  zstep.
  rewrite (jtok_is_eqb vk kind) by lia.
  destruct (Z.eqb_spec vk kind) as [EK|NK]; cbn [negb].
  2: { do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
       right. split; [intros (E & _); contradiction | reflexivity]. }
  zstep. zstep. zstep.
  rewrite (jtok_is_eqb_u vn (Z.of_nat (length T))) by lia.
  destruct (Z.eqb_spec (bv_unsigned vn) (Z.of_nat (length T))) as [EN|NN]; cbn [negb].
  2: { do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
       right. split; [intros (_ & E & _); contradiction | reflexivity]. }
  destruct (HP EK EN) as (HPb & HPl & DP). clear HP.
  apply (bytes_at_transport rsegs [(bv_unsigned sp + -32, bv_unsigned sp)] m x13 _ P) in HPb;
    [|exact MU|cbn [disjoint_from]; rewrite HPl; lia].
  pose proof (proj1 (bytes_at_app rsegs x13 (bv_unsigned a2) T (Z_to_bv 8 0 :: slack)) HT) as [HTT _].
  destruct (memcmp_model_total P T (length T) ltac:(lia) ltac:(lia)) as [v HMv].
  destruct (jtok_is_memcmp (length T) P T v HPl eq_refl HMv) as [RVv IVv].
  zstep. zstep. zstep.
  eapply evt_cut.
  { eapply BCMP with (ls := P) (rs := T) (v := v); [exact HPb | exact HTT | | exact MI0].
    rewrite unsigned_lit by lia. rewrite Nat2Z.id. exact HMv. }
  post_call rsegs x13.
  zstep. zstep.
  do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep. finish.
  destruct (Z.eq_dec v 0) as [V0|V0].
  - subst v. left. split; [split; [exact EK | split; [exact EN | apply IVv; reflexivity]] | reflexivity].
  - right. split.
    + intros (_ & _ & E). apply V0. apply IVv. exact E.
    + replace (v mod 18446744073709551616 <? 1) with false by (symmetry; apply Z.ltb_ge; Z.div_mod_to_equations; lia).
      reflexivity.
Qed.
