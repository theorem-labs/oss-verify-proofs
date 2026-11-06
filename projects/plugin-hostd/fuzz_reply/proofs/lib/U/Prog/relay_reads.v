From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Import PropExec MState Mem Exec Frame Step Tac Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.U.Prog Require Import relay_source_c relay_reads_c.
Import ListNotations.
Open Scope Z_scope.

Lemma rr_sx32_lit : forall z, -2^31 <= z < 2^31 -> sx32 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof.
  intros z Hz. unfold sx32. f_equal. rewrite unsigned_lit_wrap.
  unfold bv_swrap, bv_wrap. change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  change (2^64) with 18446744073709551616. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rr_rd8 : forall m a (v : word), bytes_at rsegs m a (le8 v) ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 8 = Some (le8 v).
Proof.
  intros m a v H. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le8 v) 0 8 H ltac:(lia)) by (rewrite length_le8; lia).
  reflexivity.
Qed.

Lemma rr_rd4 : forall m a (v : word), bytes_at rsegs m a (le4 v) ->
  ov_read_bytes rsegs m (Z_to_bv 64 a) 4 = Some (le4 v).
Proof.
  intros m a v H. change (Z_to_bv 64 a) with (wa a).
  replace (wa a) with (wa (a + 0)) by (f_equal; lia).
  rewrite (bytes_at_read rsegs m a (le4 v) 0 4 H ltac:(lia)) by (rewrite length_le4; lia).
  reflexivity.
Qed.

Lemma rr_land7 : forall x, x mod 8 = 0 -> Z.land x 7 = 0.
Proof. intros x H. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. exact H. Qed.

Lemma rr_seqz : forall z, -2^31 <= z < 2^31 -> v_sltiu (Z_to_bv 64 z) 1 = Z_to_bv 64 (if z =? 0 then 1 else 0).
Proof.
  intros z Hz. unfold v_sltiu. rewrite unsigned_lit_wrap. change (bv_wrap 64 1) with 1.
  destruct (Z.eqb_spec z 0) as [->|Hz0]; [reflexivity|].
  destruct (Z.ltb_spec (z mod 2^64) 1) as [Hl|Hl]; [|reflexivity].
  exfalso. change (2^64) with 18446744073709551616 in Hl. change (2^31) with 2147483648 in Hz.
  Z.div_mod_to_equations. lia.
Qed.

Lemma rr_entry_len : forall e, length (re_pad1 e) = 4%nat -> length (re_pad2 e) = 4%nat ->
  length (entry_bytes e) = 56%nat.
Proof.
  intros e H1 H2. unfold entry_bytes. rewrite !length_app, !length_le4, !length_le8, H1, H2. reflexivity.
Qed.

Lemma rr_table_len : forall es,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ -2^31 <= re_fd e < 2^31) es ->
  Z.of_nat (length (concat (map entry_bytes es))) = 56 * Z.of_nat (length es).
Proof.
  induction es as [|e es IH]; intros HF; [reflexivity|].
  apply Forall_cons_iff in HF. destruct HF as [(P1 & P2 & _) HF].
  cbn [map concat length]. rewrite length_app, rr_entry_len by assumption. rewrite Nat2Z.inj_add, IH by exact HF. lia.
Qed.

Lemma rr_table_nth : forall m es G i e,
  Forall (fun e => length (re_pad1 e) = 4%nat /\ length (re_pad2 e) = 4%nat /\ -2^31 <= re_fd e < 2^31) es ->
  bytes_at rsegs m G (concat (map entry_bytes es)) -> nth_error es i = Some e ->
  bytes_at rsegs m (G + 56 * Z.of_nat i) (entry_bytes e).
Proof.
  intros m es. induction es as [|e0 es IH]; intros G i e HF HB HN; [destruct i; discriminate|].
  apply Forall_cons_iff in HF. destruct HF as [(P1 & P2 & _) HF].
  cbn [map concat] in HB. apply bytes_at_app in HB. destruct HB as [HE HR].
  rewrite rr_entry_len in HR by assumption.
  destruct i as [|i]; cbn [nth_error] in HN.
  - injection HN as <-. replace (G + 56 * Z.of_nat 0) with G by lia. exact HE.
  - replace (G + 56 * Z.of_nat (S i)) with (G + 56 + 56 * Z.of_nat i) by lia. exact (IH _ i e HF HR HN).
Qed.

Lemma rr_eof_at : forall m a e, bytes_at rsegs m a (entry_bytes e) ->
  bytes_at rsegs m (a + 4) (le4 (Z_to_bv 64 (re_eof e))).
Proof.
  intros m a e H. unfold entry_bytes in H. apply bytes_at_app in H. destruct H as [_ H].
  rewrite length_le4 in H. apply bytes_at_app in H. exact (proj1 H).
Qed.

Lemma rr_src_find : forall fd es i e, src_find fd es = Some (i, e) -> nth_error es i = Some e /\ re_fd e = fd.
Proof.
  intros fd es. induction es as [|e0 es IH]; intros i e H; cbn [src_find] in H; [discriminate|].
  destruct (Z.eqb_spec (re_fd e0) fd) as [E|E].
  - injection H as <- <-. split; [reflexivity | exact E].
  - destruct (src_find fd es) as [[j e']|] eqn:Hs; [|discriminate].
    injection H as <- <-. exact (IH j e' eq_refl).
Qed.

Theorem relay_reads_holds : relay_source_contract -> relay_reads_contract.
Proof.
  intros HRS. unfold relay_reads_contract, RELAY_READS, RELAY_READS_K.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fd g es
    HZ HAl Hfd HS0 Hlen HN HG HT HEof HGn MI ST LO D0 DN DG DT.
  pose proof ST as (L0 & L1 & _).
  pose proof (bv_unsigned_in_range 64 g) as Rg. unfold bv_modulus in Rg.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
  unfold G_NSRC, G_SRC in *.
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
  assert (RDra : ov_read_bytes rsegs M1 (Z_to_bv 64 (bv_unsigned sp + -8)) 8 = Some (le8 ra)).
  { apply rr_rd8. subst M1. change (Z_to_bv 64 (bv_unsigned sp + -8)) with (wa (bv_unsigned sp + -8)).
    apply bytes_at_write_same; [lia | rewrite length_le8; lia]. }
  assert (MU1 : munch [(bv_unsigned sp - 16, bv_unsigned sp)] m M1).
  { subst M1. change (Z_to_bv 64 (bv_unsigned sp + -8)) with (wa (bv_unsigned sp + -8)).
    apply munch_write; [apply munch_refl | lia | rewrite length_le8; lia | cbn [inside]; left; rewrite length_le8; lia]. }
  assert (WM1 : wmono rsegs m M1).
  { subst M1. apply wmono_write, wmono_refl. }
  assert (ST1 : stk rsegs M1 lo (bv_unsigned sp)).
  { subst M1. change (Z_to_bv 64 (bv_unsigned sp + -8)) with (wa (bv_unsigned sp + -8)).
    apply stk_write; [exact ST | lia | rewrite length_le8; lia]. }
  assert (MI1 : mem_inv rsegs M1).
  { subst M1. apply mem_inv_store; [exact MI | rewrite length_le8; exact SOK]. }
  assert (HS1 : bytes_at rsegs M1 (bv_unsigned a0) (le4 (Z_to_bv 64 fd))).
  { apply W1; [exact HS0 | rewrite length_le4; lia]. }
  assert (HN1 : bytes_at rsegs M1 0x318b8 (le4 (Z_to_bv 64 (Z.of_nat (length es))))).
  { apply W1; [exact HN | rewrite length_le4; lia]. }
  assert (HG1 : bytes_at rsegs M1 0x318d0 (le8 g)).
  { apply W1; [exact HG | rewrite length_le8; lia]. }
  destruct HT as [HF HB].
  assert (HB1 : bytes_at rsegs M1 (bv_unsigned g) (concat (map entry_bytes es))).
  { destruct es as [|e0 es0].
    - cbn [map concat]. split; [lia|]. split; [cbn [length]; lia|]. intros i Hi. cbn [length] in Hi. lia.
    - apply W1; [exact HB|]. rewrite (rr_table_len _ HF). pose proof (DT ltac:(congruence)) as D. lia. }
  assert (RD0 : ov_read_bytes rsegs M1 a0 4 = Some (le4 (Z_to_bv 64 fd))).
  { rewrite <- (Z_to_bv_lit_self a0). apply rr_rd4. exact HS1. }
  step. step.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    replace mm with M1 by (subst M1; f_equal; word_eq_tac) end.
  step. if_false.
  step. rewrite (rr_land7 (bv_unsigned a0) HAl).
  step. if_false.
  step. rewrite (rr_sx32_lit fd) by lia.
  step.
  eapply evt_cut.
  { eapply HRS with (fd := fd) (g := g) (es := es);
      [exact Hfd | reflexivity | exact Hlen | exact HN1 | exact HG1 | split; [exact HF | exact HB1] | exact HGn]. }
  intros ms' (a1' & a2' & a3' & a4' & a5' & a6' & a7' & ->).
  replace (ret_pc (Z_to_bv 64 0x1536c)) with (Z_to_bv 64 0x1536c) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
  unfold relay_source_r, relay_reads_r.
  destruct (src_find fd es) as [[i e]|] eqn:Hsf.
  - destruct (rr_src_find fd es i e Hsf) as [Hnth Hfe].
    assert (Hne : es <> []) by (intros ->; destruct i; discriminate).
    destruct (HGn Hne) as [GZ GA].
    pose proof (rr_table_nth M1 es (bv_unsigned g) i e HF HB1 Hnth) as HE.
    pose proof (bytes_at_bound _ _ _ _ HE) as BE.
    rewrite rr_entry_len in BE by (apply Forall_forall with (x := e) in HF; [tauto | eapply nth_error_In; exact Hnth]).
    pose proof (rr_eof_at M1 _ e HE) as HEo.
    pose proof (rr_rd4 M1 _ _ HEo) as RDe.
    assert (Reof : -2^31 <= re_eof e < 2^31).
    { apply Forall_forall with (x := e) in HEof; [exact HEof | eapply nth_error_In; exact Hnth]. }
    assert (UR : bv_unsigned (Z_to_bv 64 (bv_unsigned g + 56 * Z.of_nat i)) = bv_unsigned g + 56 * Z.of_nat i).
    { apply unsigned_lit. lia. }
    assert (Hm8 : (bv_unsigned g + 56 * Z.of_nat i) mod 8 = 0).
    { rewrite Z.add_mod by lia. rewrite GA. replace (56 * Z.of_nat i) with (Z.of_nat i * 7 * 8) by lia.
      rewrite Z.mod_mul by lia. reflexivity. }
    step. if_cases Hc1.
    + exfalso. unfold bv_eqb in Hc1. rewrite UR in Hc1. apply Z.eqb_eq in Hc1. fold_lit_ux_in Hc1. lia.
    + step. rewrite ?UR. rewrite (rr_land7 _ Hm8).
      step. if_false.
      step. rewrite (rr_sx32_lit (re_eof e)) by lia.
      step. rewrite (rr_seqz (re_eof e)) by lia.
      step. step. step.
      apply evt_done. do 8 eexists. split; [reflexivity|].
      split; [exact MU1 | split; [exact WM1 | split; [exact MI1 | exact ST1]]].
  - step. if_true.
    step. step. step.
    apply evt_done. do 8 eexists. split; [reflexivity|].
    split; [exact MU1 | split; [exact WM1 | split; [exact MI1 | exact ST1]]].
Qed.
