From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import check_bounded_c.
Import ListNotations.
Open Scope Z_scope.

Lemma sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Lemma rd8 : forall m a (v : word) e, bytes_at rsegs m a (le8 v) -> e = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 e) 8 = Some (le8 v).
Proof.
  intros m a v e H ->. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia)) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma rd4 : forall m a (v : word) e, bytes_at rsegs m a (le4 v) -> e = a ->
  ov_read_bytes rsegs m (Z_to_bv 64 e) 4 = Some (le4 v).
Proof.
  intros m a v e H ->. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia)) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma shr5_lt : forall cp : word, bv_unsigned cp < 20192 ->
  bv_ltu (Z_to_bv 64 (Z.shiftr (bv_unsigned cp) 5)) (Z_to_bv 64 631) = true.
Proof.
  intros cp H. pose proof (bv_unsigned_in_range 64 cp) as R. unfold bv_modulus in R.
  unfold bv_ltu. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
  rewrite (unsigned_lit (bv_unsigned cp / 32)) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  rewrite (unsigned_lit 631) by lia. apply Z.ltb_lt. apply Z.div_lt_upper_bound; lia.
Qed.

Lemma cb_loop : forall (c : nat) (k j A P : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  k = Z.of_nat (S c) -> k < 2^31 -> A = P + 56 * j + 32 ->
  (forall i, j <= i < j + k -> source_bounded m P i) ->
  evt rsegs
    (fun ms' => exists a0' a2' a4' a5' : word,
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 6000) a2' (Z_to_bv 64 631) a4' a5' a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (Z_to_bv 64 0x143b0) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 k) (Z_to_bv 64 6000) (Z_to_bv 64 A) (Z_to_bv 64 631) a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1438c) fc None m (seg_rom rsegs)).
Proof.
  induction c as [|c IH];
    intros k j A P ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      Hk Hk2 HA HR.
  - pose proof (HR j ltac:(lia)) as SB. unfold source_bounded in SB.
    destruct SB as (u & cp & Bu & Bc & U1 & U2 & U3).
    pose proof (rd8 m _ u (A + -8) Bu ltac:(lia)) as RD1.
    pose proof (rd8 m _ cp A Bc ltac:(lia)) as RD2.
    step. step. if_false.
    step. step. if_false.
    step. step. rewrite (shr5_lt cp U3). cbn [negb].
    step. step. step. if_cases HB.
    + exfalso. zify_cond HB. lia.
    + apply evt_done. do 4 eexists. reflexivity.
  - pose proof (HR j ltac:(lia)) as SB. unfold source_bounded in SB.
    destruct SB as (u & cp & Bu & Bc & U1 & U2 & U3).
    pose proof (rd8 m _ u (A + -8) Bu ltac:(lia)) as RD1.
    pose proof (rd8 m _ cp A Bc ltac:(lia)) as RD2.
    step. step. if_false.
    step. step. if_false.
    step. step. rewrite (shr5_lt cp U3). cbn [negb].
    step. step. step. if_cases HB.
    + eapply (IH (k + -1) (j + 1) (A + 56) P); [lia | lia | lia | intros i Hi; apply HR; lia].
    + exfalso. zify_cond HB. lia.
Qed.

Theorem check_bounded_holds : check_bounded_contract.
Proof.
  unfold check_bounded_contract, CHECK_BOUNDED, CHECK_BOUNDED_FRAME, G_NSRC, G_SRC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo n src
    ST LO Hn HN HS HR DN DS DR.
  pose proof ST as (L0 & L1 & _).
  remember (write_to_mem m (Z_to_bv 64 (bv_unsigned sp + -8)) (le8 ra)) as M1 eqn:EM.
  assert (W1 : forall c cs, bytes_at rsegs m c cs ->
            c + Z.of_nat (length cs) <= bv_unsigned sp - 8 \/ bv_unsigned sp <= c ->
            bytes_at rsegs M1 c cs).
  { intros c cs Hc Hd. subst M1. change (Z_to_bv 64 (bv_unsigned sp + -8)) with (wa (bv_unsigned sp + -8)).
    apply bytes_at_write_other; [exact Hc | lia | rewrite length_le8; lia | rewrite length_le8; lia]. }
  assert (SOK : store_ok rsegs m (Z_to_bv 64 (bv_unsigned sp + -8)) 8 = true).
  { replace (bv_unsigned sp + -8) with (bv_unsigned sp - 16 + 8) by lia.
    apply (wr_at_store_ok rsegs m (bv_unsigned sp - 16) 16 8 8%nat); [ | lia | lia].
    destruct ST as (_ & _ & ST3). split; [lia|]. split; [lia|].
    intros i Hi. apply (proj1 (ST3 (bv_unsigned sp - 16 + i) ltac:(lia))). }
  assert (RDn : ov_read_bytes rsegs M1 (Z_to_bv 64 0x30fd8) 4 = Some (le4 (Z_to_bv 64 n))).
  { apply rd4 with (a := 0x30fd8); [apply W1; [exact HN | rewrite length_le4; lia] | reflexivity]. }
  assert (RDs : ov_read_bytes rsegs M1 (Z_to_bv 64 0x30ff0) 8 = Some (le8 src)).
  { apply rd8 with (a := 0x30ff0); [apply W1; [exact HS | rewrite length_le8; lia] | reflexivity]. }
  assert (RDra : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned sp + -8)) 8 = Some (le8 ra)).
  { apply rd8 with (a := bv_unsigned sp + -8); [ | reflexivity].
    subst M1. change (Z_to_bv 64 (bv_unsigned sp + -8)) with (wa (bv_unsigned sp + -8)).
    apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
  assert (HR1 : forall i, 0 <= i < 0 + n -> source_bounded M1 (bv_unsigned src) i).
  { intros i Hi. pose proof (HR i ltac:(lia)) as SB. pose proof (DR i ltac:(lia)) as D.
    unfold source_bounded in *. destruct SB as (u & cp & Bu & Bc & U).
    exists u, cp. split; [|split; [|exact U]].
    - apply W1; [exact Bu | rewrite length_le8; lia].
    - apply W1; [exact Bc | rewrite length_le8; lia]. }
  assert (MU1 : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m M1).
  { subst M1. change (Z_to_bv 64 (bv_unsigned sp + -8)) with (wa (bv_unsigned sp + -8)).
    apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia | cbn [inside]; left; rewrite length_le8; lia]. }
  assert (WM1 : wmono rsegs m M1).
  { subst M1. apply wmono_write, wmono_refl. }
  assert (ST1 : stk rsegs M1 lo (bv_unsigned sp)).
  { subst M1. change (Z_to_bv 64 (bv_unsigned sp + -8)) with (wa (bv_unsigned sp + -8)).
    apply stk_write; [exact ST | lia | rewrite length_le8; lia]. }
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    replace mm with M1 by (subst M1; f_equal; word_eq_tac) end.
  step. step. step. rewrite (sx32_lit n) by lia.
  step. if_cases HC.
  - step. step. step.
    apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU1 | split; [exact WM1 | exact ST1]].
  - assert (Hp : 0 < n).
    { unfold bv_lts in HC. rewrite (signed_lit 0), (signed_lit n) in HC by lia.
      apply Bool.negb_false_iff, Z.ltb_lt in HC. exact HC. }
    step. step. step. step. step.
    eapply evt_cut.
    { eapply (cb_loop (Z.to_nat (n - 1)) n 0 (bv_unsigned src + 32) (bv_unsigned src)); [lia | lia | lia | exact HR1]. }
    intros ms' (a0' & a2' & a4' & a5' & ->).
    step. step. step.
    apply evt_done. do 7 eexists. split; [reflexivity|]. split; [exact MU1 | split; [exact WM1 | exact ST1]].
Qed.
