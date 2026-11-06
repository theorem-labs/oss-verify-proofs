From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import relay_source_c.
Import ListNotations.
Open Scope Z_scope.

Lemma rs_sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rs_signed_lit : forall z, -2^63 <= z < 2^63 -> bv_signed (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite zb_signed, unsigned_lit_wrap.
  change (2^64) with 18446744073709551616. change (2^63) with 9223372036854775808 in *.
  destruct (Z.ltb_spec (z mod 18446744073709551616) 9223372036854775808); cbv iota;
    Z.div_mod_to_equations; lia.
Qed.

Lemma rs_rd8 : forall m a (v : word), bytes_at rsegs m a (le8 v) ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 8 = Some (le8 v).
Proof.
  intros m a v H. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia)) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma rs_rd4 : forall m a (v : word), bytes_at rsegs m a (le4 v) ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 4 = Some (le4 v).
Proof.
  intros m a v H. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia)) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma rs_sltu0 : forall x : word, bv_unsigned x <> 0 -> v_sltu (Z_to_bv 64 0) x = Z_to_bv 64 1.
Proof.
  intros x H. pose proof (bv_unsigned_in_range 64 x) as R. unfold bv_modulus in R.
  rewrite v_sltu_b2z. change (bv_unsigned (Z_to_bv 64 0)) with 0.
  destruct (Z.ltb_spec 0 (bv_unsigned x)); [reflexivity | lia].
Qed.

Lemma rs_sltiu1_pos : forall B, 0 < B < 2^64 -> v_sltiu (Z_to_bv 64 B) 1 = Z_to_bv 64 0.
Proof.
  intros B HB. unfold v_sltiu. rewrite (unsigned_lit B) by lia. change (bv_wrap 64 1) with 1.
  destruct (Z.ltb_spec B 1); [lia | reflexivity].
Qed.

Lemma rs_seqz0 : v_sltiu (Z_to_bv 64 0) 1 = Z_to_bv 64 1.
Proof.
  unfold v_sltiu. change (bv_unsigned (Z_to_bv 64 0)) with 0. change (bv_wrap 64 1) with 1. reflexivity.
Qed.

Lemma rs_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma rs_eqb_neq : forall x y, -2^31 <= x < 2^31 -> -2^31 <= y < 2^31 -> x <> y ->
  bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 y) = false.
Proof.
  intros x y Hx Hy Hne. unfold bv_eqb. rewrite !unsigned_lit_wrap. apply Z.eqb_neq.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hx, Hy.
  intro E. apply Hne. Z.div_mod_to_equations. lia.
Qed.

Lemma rs_eqb_eq : forall x, bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 x) = true.
Proof. intros x. unfold bv_eqb. apply Z.eqb_eq. reflexivity. Qed.

Lemma entry_bytes_length : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes. rewrite !length_app, !length_le4, !length_le8, H1, H2. reflexivity.
Qed.

Lemma table_cons : forall m B e es, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  bytes_at rsegs m B (concat (map entry_bytes (e :: es))) ->
  bytes_at rsegs m B (le4 (Z_to_bv 64 (re_fd e))) /\ bytes_at rsegs m (B + 56) (concat (map entry_bytes es)).
Proof.
  intros m B e es H1 H2 H. cbn [map concat] in H. apply bytes_at_app in H. destruct H as [HE HR].
  rewrite entry_bytes_length in HR by assumption. split; [|exact HR].
  unfold entry_bytes in HE. apply bytes_at_app in HE. exact (proj1 HE).
Qed.

Lemma rsr_nil : forall B fd, relay_source_r B fd [] = 0.
Proof. reflexivity. Qed.

Lemma rsr_hit : forall B fd e es, re_fd e = fd -> relay_source_r B fd (e :: es) = B.
Proof.
  intros B fd e es H. unfold relay_source_r. cbn [src_find]. rewrite (proj2 (Z.eqb_eq _ _) H). lia.
Qed.

Lemma rsr_miss : forall B fd e es, re_fd e <> fd -> relay_source_r B fd (e :: es) = relay_source_r (B + 56) fd es.
Proof.
  intros B fd e es H. unfold relay_source_r. cbn [src_find]. rewrite (proj2 (Z.eqb_neq _ _) H).
  destruct (src_find fd es) as [[i e']|]; [|reflexivity]. lia.
Qed.

Lemma rs_loop : forall (es : list rentry) (k B fd : Z) (g x1 x2 x4 x5 x6 x7 : word)
    (ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
  es <> [] -> k = Z.of_nat (length es) -> k < 2^31 ->
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ -2^31 <= re_fd e < 2^31) es ->
  bytes_at rsegs m B (concat (map entry_bytes es)) ->
  0 < bv_unsigned g <= B -> -2^31 <= fd < 2^31 ->
  x1 = Z_to_bv 64 B -> x2 = Z_to_bv 64 k -> x4 = Z_to_bv 64 1 -> x5 = Z_to_bv 64 1 -> x6 = Z_to_bv 64 B ->
  evt rsegs
    (fun ms' => exists (a1' a2' a3' a4' a5' a6' a7' : word),
       ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (relay_source_r B fd es))
                     a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                F (ret_pc ra) fc None m (seg_rom rsegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 fd) x1 x2 g x4 x5 x6 x7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x14ea4) fc None m (seg_rom rsegs)).
Proof.
  induction es as [|e es IH];
    intros k B fd g x1 x2 x4 x5 x6 x7 ra sp gp tp t0 t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
      Hne Hk Hk2 HF HB HG Hfd E1 E2 E4 E5 E6; [congruence|].
  subst x1 x2 x4 x5 x6.
  apply Forall_cons_iff in HF. destruct HF as [(P1 & P2 & Rfd) HF].
  destruct (table_cons m B e es P1 P2 HB) as [HE HR].
  pose proof (bytes_at_bound _ _ _ _ HR) as BR.
  pose proof (rs_rd4 m B _ HE) as RD.
  assert (UB : bv_unsigned (Z_to_bv 64 B) = B) by (apply unsigned_lit; lia).
  step. if_cases Hc1.
  - exfalso. unfold bv_ltu in Hc1. rewrite UB in Hc1. apply Z.ltb_lt in Hc1. lia.
  - step. rewrite (rs_sltiu1_pos B) by lia.
    step. step. if_false.
    step. if_false.
    step. rewrite (rs_sx32_lit (re_fd e)) by lia.
    step.
    destruct (Z.eq_dec (re_fd e) fd) as [Hq|Hq].
    + subst fd. if_true_by (rs_eqb_eq (re_fd e)).
      step. step. rewrite rsr_hit by reflexivity.
      apply evt_done. do 7 eexists. reflexivity.
    + if_false_by (rs_eqb_neq (re_fd e) fd Rfd Hfd Hq).
      rewrite rsr_miss by exact Hq.
      step. step. step. step. if_cases Hc2.
      * destruct es as [|e2 es2].
        { exfalso. zify_cond Hc2. cbn [length] in Hk. lia. }
        eapply (IH (k + -1) (B + 56));
          first [ reflexivity | congruence | exact HF | exact HR | (cbn [length] in Hk |- *; lia) | lia
                | (f_equal; lia) | idtac ].
      * destruct es as [|e2 es2].
        -- step. step. step. rewrite rsr_nil.
           apply evt_done. do 7 eexists. reflexivity.
        -- exfalso. zify_cond Hc2. cbn [length] in Hk. lia.
Qed.

Theorem relay_source_holds : relay_source_contract.
Proof.
  unfold relay_source_contract, RELAY_SOURCE, G_NSRC, G_SRC.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m fd g es
    Hfd Ha0 Hlen HN HS [HF HT] HG.
  subst a0.
  pose proof (rs_rd4 m _ _ HN) as RDn.
  pose proof (rs_rd8 m _ _ HS) as RDs.
  pose proof (bv_unsigned_in_range 64 g) as Rg. unfold bv_modulus in Rg.
  step. step. step. rewrite (rs_sx32_lit (Z.of_nat (length es))) by lia.
  step. if_cases HC.
  - assert (E0 : es = []).
    { unfold bv_lts in HC. rewrite (rs_signed_lit 0), (rs_signed_lit (Z.of_nat (length es))) in HC by lia.
      apply Bool.negb_true_iff, Z.ltb_ge in HC. destruct es; [reflexivity | cbn [length] in HC; lia]. }
    subst es. step. step. step. apply evt_done. do 7 eexists. reflexivity.
  - assert (Hp : es <> []).
    { unfold bv_lts in HC. rewrite (rs_signed_lit 0), (rs_signed_lit (Z.of_nat (length es))) in HC by lia.
      apply Bool.negb_false_iff, Z.ltb_lt in HC. destruct es; [cbn in HC; lia | congruence]. }
    destruct (HG Hp) as (HZ & HAl).
    step. step. rewrite (rs_sltu0 g HZ).
    step. rewrite (rs_land7 (bv_unsigned g) HAl).
    step. rewrite rs_seqz0.
    step. step. step.
    pose proof (bytes_at_bound _ _ _ _ HT) as BT.
    eapply (rs_loop es (Z.of_nat (length es)) (bv_unsigned g) fd g);
      first [ reflexivity | exact Hp | exact HF | exact HT | lia | (symmetry; apply Z_to_bv_lit_self)
            | (f_equal; lia) | idtac ].
Qed.
