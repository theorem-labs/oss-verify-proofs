From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_rival_kind_of_c.
Import ListNotations.
Open Scope Z_scope.

Lemma bytes_at_read0 : forall m a bs, bytes_at rsegs m a bs -> ov_read_bytes rsegs m (wa a) (length bs) = Some bs.
Proof.
  intros m a bs H. pose proof H as (H0 & H1 & _).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a bs 0 (length bs) H) by lia.
  f_equal. apply firstn_all.
Qed.

Lemma sx32_lit : forall v, -2^31 <= v < 2^31 -> sx32 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold sx32. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma sx32_u : forall c, 0 <= c < 2^32 -> sx32 (Z_to_bv 64 c) = Z_to_bv 64 (c - 2^32 * (c / 2^31)).
Proof.
  intros c Hc. unfold sx32. f_equal. rewrite unsigned_lit_wrap. unfold bv_swrap, bv_wrap.
  replace (bv_half_modulus 32) with 2147483648 by reflexivity.
  replace (bv_modulus 32) with 4294967296 by reflexivity.
  Z.div_mod_to_equations. lia.
Qed.

Lemma zxb_lit : forall d, 0 <= d < 2^8 -> zxb (Z_to_bv 8 d) = Z_to_bv 64 d.
Proof.
  intros d Hd. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. exact Hd.
Qed.

Ltac zc HC := unfold bv_eqb, bv_ltu in HC; rewrite ?unsigned_lit_wrap in HC; zify_bool HC; Z.div_mod_to_equations; lia.

Ltac rleaf k :=
  lazymatch goal with
  | |- context [reac_rival_kind_model ?d ?r ?s ?c] =>
      replace (reac_rival_kind_model d r s c) with k
        by (unfold reac_rival_kind_model;
            repeat match goal with H : ?b = false |- context [?b] => rewrite H end;
            decide_tests; reflexivity);
      apply evt_done; do 5 eexists; reflexivity
  end.

Theorem reac_rival_kind_of_holds : reac_rival_kind_of_contract.
Proof.
  unfold reac_rival_kind_of_contract, REAC_RIVAL_KIND_OF.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e r d s c E He H8 HF. subst a0.
  step.
  if_cases HC.
  - assert (E0 : e = 0) by zc HC. subst e. clear HC.
    step. apply evt_done. do 5 eexists. reflexivity.
  - assert (Ne : e <> 0) by zc HC. clear HC.
    rewrite (proj2 (Z.eqb_neq e 0) Ne). cbv iota.
    destruct (HF Ne) as (Hr & Hd & Hs & Hc & B8 & B12 & B16 & B20). clear HF.
    pose proof (bytes_at_read0 m _ _ B8) as R8. change (ov_read_bytes rsegs m (wa (e + 8)) 4 = Some (le4 (Z_to_bv 64 r))) in R8.
    pose proof (bytes_at_read0 m _ _ B12) as R12. change (ov_read_bytes rsegs m (wa (e + 12)) 1 = Some [Z_to_bv 8 d]) in R12.
    pose proof (bytes_at_read0 m _ _ B16) as R16. change (ov_read_bytes rsegs m (wa (e + 16)) 1 = Some [Z_to_bv 8 s]) in R16.
    pose proof (bytes_at_read0 m _ _ B20) as R20. change (ov_read_bytes rsegs m (wa (e + 20)) 4 = Some (le4 (Z_to_bv 64 c))) in R20.
    step. step. rewrite (zxb_lit d) by lia. step. step.
    if_cases HC1.
    2: { assert (D0 : d <> 0) by zc HC1. clear HC1. step. rleaf 2. }
    assert (D0 : d = 0) by zc HC1. clear HC1.
    step. rewrite (sx32_lit r) by lia. step. step.
    if_cases HC2.
    { assert (R1 : r = 1) by zc HC2. clear HC2. step. rleaf 2. }
    assert (R1 : r <> 1) by zc HC2. clear HC2.
    step. rewrite (zxb_lit s) by lia. step. step. step.
    if_cases HC3.
    { assert (S1 : 1 <= s < 40) by zc HC3. clear HC3. step. rleaf 2. }
    assert (S1' : s = 0 \/ 40 <= s) by zc HC3. clear HC3.
    assert (S1 : (1 <=? s) && (s <? 40) = false).
    { destruct S1' as [-> | S40]; [reflexivity | rewrite (proj2 (Z.ltb_ge s 40) S40), andb_false_r; reflexivity]. }
    step. rewrite (sx32_u c) by lia. step.
    if_cases HC4.
    { assert (C0 : c = 0) by zc HC4. clear HC4. step. step. rleaf 3. }
    assert (C0 : c <> 0) by zc HC4. clear HC4.
    step. step.
    if_cases HC5.
    { assert (C1 : c < 40) by zc HC5. clear HC5. step. rleaf 2. }
    assert (C1 : 40 <= c) by zc HC5. clear HC5.
    step. step. step.
    if_cases HC6.
    { assert (R2 : r <> 2) by zc HC6. clear HC6. step. rleaf 3. }
    assert (R2 : r = 2) by zc HC6. clear HC6.
    step. step.
    if_cases HC7.
    { assert (S4 : s = 40) by zc HC7. clear HC7. step. step. rleaf 1. }
    assert (S4 : s <> 40) by zc HC7. clear HC7.
    step. step. rleaf 4.
Qed.
