From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require hex4_c hex4.
Import ListNotations.
Open Scope Z_scope.

Lemma psl_skipn_nth : forall (A : Type) (l : list A) k c, nth_error l k = Some c -> skipn k l = c :: skipn (S k) l.
Proof.
  intros A l. induction l as [|h t IH]; intros k c H; destruct k; cbn in *; try discriminate.
  - injection H as ->. reflexivity.
  - apply IH. exact H.
Qed.

Lemma psl_rest_cons : forall tb text x c, text <= x -> nth_error tb (Z.to_nat (x - text)) = Some c ->
  rest_at tb text x = bv_unsigned c :: rest_at tb text (x + 1).
Proof.
  intros tb text x c Hx Hc. unfold rest_at, zb. rewrite (psl_skipn_nth _ tb _ c Hc). cbn [map].
  replace (Z.to_nat (x + 1 - text)) with (S (Z.to_nat (x - text))) by lia. reflexivity.
Qed.

Lemma psl_rest_end : forall tb text x, Z.of_nat (length tb) <= x - text -> rest_at tb text x = [].
Proof.
  intros tb text x Hx. unfold rest_at, zb. rewrite skipn_all2 by lia. reflexivity.
Qed.

Lemma psl_read : forall m text tb x c, bytes_at rsegs m text tb -> text <= x ->
  nth_error tb (Z.to_nat (x - text)) = Some c -> ov_read_bytes rsegs m (wa x) 1 = Some [c].
Proof.
  intros m text tb x c HB Hx Hc.
  assert (Hk : (Z.to_nat (x - text) < length tb)%nat) by (apply nth_error_Some; rewrite Hc; discriminate).
  replace x with (text + (x - text)) at 1 by lia.
  rewrite (bytes_at_read rsegs m text tb (x - text) 1 HB) by lia.
  rewrite (psl_skipn_nth _ tb _ c Hc). reflexivity.
Qed.

Local Ltac cond_fact H := zify_cond H; rewrite ?unsigned_lit_wrap in H.

Lemma psl_scan_q : forall r, scan (34 :: r) = Some 0%nat.
Proof. reflexivity. Qed.

Lemma psl_scan_bs1 : scan [92] = None.
Proof. reflexivity. Qed.

Lemma psl_ltu : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> bv_ltu (Z_to_bv 64 a) (Z_to_bv 64 b) = (a <? b).
Proof. intros a b Ha Hb. unfold bv_ltu. rewrite !unsigned_lit by lia. reflexivity. Qed.

Lemma psl_seqz : forall c : byte, 0 <= bv_unsigned c < 256 ->
  bv_unsigned (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -92)) 1) = if bv_unsigned c =? 92 then 1 else 0.
Proof.
  intros c Hc. rewrite v_sltiu_b2z. unfold zxb. rewrite (unsigned_lit (bv_unsigned c)) by lia.
  change (bv_wrap 64 1) with 1. rewrite (unsigned_lit_wrap (bv_unsigned c + -92)).
  destruct (Z.eqb_spec (bv_unsigned c) 92) as [E|E].
  - rewrite E. reflexivity.
  - replace ((bv_unsigned c + -92) mod 2 ^ 64 <? 1) with false; [reflexivity|].
    symmetry. apply Z.ltb_ge. Z.div_mod_to_equations. lia.
Qed.

Lemma psl_not : forall x, 0 <= x < 2 ^ 64 -> Z.lxor x 18446744073709551615 = 2 ^ 64 - 1 - x.
Proof.
  intros x Hx. change 18446744073709551615 with (Z.ones 64).
  assert (H0 : Z.ldiff x (Z.ones 64) = 0).
  { apply Z.bits_inj'. intros n Hn. rewrite Z.ldiff_spec, Z.testbit_ones_nonneg, Z.bits_0 by lia.
    destruct (Z.ltb_spec n 64); [rewrite andb_false_r; reflexivity|].
    rewrite <- (Z.mod_small x (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity. }
  replace (2 ^ 64 - 1 - x) with (Z.ones 64 - x) by (rewrite Z.ones_equiv; lia).
  rewrite (Z.sub_nocarry_ldiff (Z.ones 64) x H0).
  apply Z.bits_inj'. intros n Hn. rewrite Z.lxor_spec, Z.ldiff_spec, Z.testbit_ones_nonneg by lia.
  destruct (Z.ltb_spec n 64); cbn [andb].
  - destruct (Z.testbit x n); reflexivity.
  - rewrite <- (Z.mod_small x (2 ^ 64)) by lia. rewrite Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma ps_scan_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (text len x : Z) (tb : list byte),
  a0 = Z_to_bv 64 (text + len) -> a2 = Z_to_bv 64 34 -> a1 = Z_to_bv 64 x ->
  bytes_at rsegs m text tb -> Z.of_nat (length tb) = len -> text + len < 2 ^ 62 -> text <= x < text + len ->
  evt rsegs
    (fun ms' => match scan (rest_at tb text x) with
       | Some Q => exists a3' a4' : word,
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (x + Z.of_nat Q)) a2 a3' a4' a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17084) fc None m (seg_rom rsegs)
       | None => exists a1' a3' a4' : word,
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3' a4' a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x172dc) fc None m (seg_rom rsegs)
       end)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1705c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m text len x tb
    E0 E2 E1 HB HL Hend Hx.
  pose proof (bytes_at_bound rsegs m text tb HB) as [Ht _].
  subst a0 a2.
  remember (Z.to_nat (text + len - x)) as n eqn:Hn.
  revert x a1 a3 a4 E1 Hx Hn.
  induction n as [n IH] using lt_wf_ind.
  intros x a1 a3 a4 E1 Hx Hn. subst a1.
  destruct (nth_error tb (Z.to_nat (x - text))) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  pose proof (psl_read m text tb x c HB ltac:(lia) Hc) as RD.
  pose proof (psl_rest_cons tb text x c ltac:(lia) Hc) as HR.
  assert (HZ : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  step. step.
  if_cases HC1.
  - cond_fact HC1. rewrite Z.mod_small in HC1 by lia.
    apply evt_done. cbv beta. rewrite HR, HC1, psl_scan_q. cbv beta iota.
    replace (x + Z.of_nat 0) with x by lia. do 2 eexists. reflexivity.
  - cond_fact HC1. rewrite Z.mod_small in HC1 by lia.
    step. step. step. step. step.
    rewrite (psl_seqz c HZ), (unsigned_lit x), psl_not by lia.
    destruct (Z.eqb_spec (bv_unsigned c) 92) as [B|B].
    + rewrite (psl_ltu (2 ^ 64 - 1 - x) (1 + 1)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv iota.
      step. step.
      rewrite (psl_ltu (x + 2) (text + len)) by lia.
      rewrite HR, B.
      destruct (Z.ltb_spec (x + 2) (text + len)) as [L|L]; cbv iota.
      * destruct (nth_error tb (Z.to_nat (x + 1 - text))) as [e|] eqn:He; [|apply nth_error_None in He; lia].
        rewrite (psl_rest_cons tb text (x + 1) e ltac:(lia) He), scan_bs.
        replace (x + 1 + 1) with (x + 2) by lia.
        eapply evt_mono.
        { apply (IH (Z.to_nat (text + len - (x + 2))) ltac:(lia) (x + 2) _ _ _ eq_refl ltac:(lia) eq_refl). }
        intros ms' Hms. cbv beta in Hms |- *.
        destruct (scan (rest_at tb text (x + 2))) as [Q|]; cbn [option_map].
        -- destruct Hms as (a3' & a4' & ->). exists a3', a4'.
           replace (x + Z.of_nat (S (S Q))) with (x + 2 + Z.of_nat Q) by lia. reflexivity.
        -- exact Hms.
      * step. apply evt_done. cbv beta.
        destruct (Z.ltb_spec (x + 1) (text + len)) as [L1|L1].
        -- destruct (nth_error tb (Z.to_nat (x + 1 - text))) as [e|] eqn:He; [|apply nth_error_None in He; lia].
           rewrite (psl_rest_cons tb text (x + 1) e ltac:(lia) He), scan_bs.
           rewrite (psl_rest_end tb text (x + 1 + 1)) by lia.
           cbn [scan option_map]. do 3 eexists. reflexivity.
        -- rewrite (psl_rest_end tb text (x + 1)) by lia.
           rewrite psl_scan_bs1. cbv beta iota. do 3 eexists. reflexivity.
    + rewrite (psl_ltu (2 ^ 64 - 1 - x) (0 + 1)) by lia. rewrite (proj2 (Z.ltb_ge _ _)) by lia. cbv iota.
      step. step.
      rewrite (psl_ltu (x + 1) (text + len)) by lia.
      rewrite HR, (scan_ndq (bv_unsigned c) _ HC1 B).
      destruct (Z.ltb_spec (x + 1) (text + len)) as [L|L]; cbv iota.
      * eapply evt_mono.
        { apply (IH (Z.to_nat (text + len - (x + 1))) ltac:(lia) (x + 1) _ _ _ eq_refl ltac:(lia) eq_refl). }
        intros ms' Hms. cbv beta in Hms |- *.
        destruct (scan (rest_at tb text (x + 1))) as [Q|]; cbn [option_map].
        -- destruct Hms as (a3' & a4' & ->). exists a3', a4'.
           replace (x + Z.of_nat (S Q)) with (x + 1 + Z.of_nat Q) by lia. reflexivity.
        -- exact Hms.
      * step. apply evt_done. cbv beta.
        rewrite (psl_rest_end tb text (x + 1)) by lia.
        cbn [scan option_map]. do 3 eexists. reflexivity.
Qed.

Lemma ps_scan : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (text len s : Z) (tb : list byte),
  a0 = Z_to_bv 64 (text + len) -> s3 = Z_to_bv 64 s ->
  bytes_at rsegs m text tb -> Z.of_nat (length tb) = len -> text + len < 2 ^ 62 -> text <= s <= text + len ->
  evt rsegs
    (fun ms' => match scan (rest_at tb text s) with
       | Some Q => exists a3' a4' : word,
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 (s + Z.of_nat Q)) (Z_to_bv 64 34) a3' a4' a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x17084) fc None m (seg_rom rsegs)
       | None => exists a1' a2' a3' a4' : word,
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x172dc) fc None m (seg_rom rsegs)
       end)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x17050) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m text len s tb
    E0 E3 HB HL Hend Hs.
  pose proof (bytes_at_bound rsegs m text tb HB) as [Ht _].
  subst a0 s3.
  step.
  if_cases HC1.
  - cond_fact HC1.
    apply evt_done. cbv beta.
    rewrite (psl_rest_end tb text s) by lia. cbn [scan].
    do 4 eexists. reflexivity.
  - cond_fact HC1.
    step. step.
    eapply evt_mono.
    { apply (ps_scan_loop ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (text + len)) (Z_to_bv 64 s) (Z_to_bv 64 34) a3 a4 a5 a6 a7
               s2 (Z_to_bv 64 s) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m text len s tb
               eq_refl eq_refl eq_refl HB HL Hend ltac:(lia)). }
    intros ms' Hms. cbv beta in Hms |- *.
    destruct (scan (rest_at tb text s)) as [Q|].
    + destruct Hms as (a3' & a4' & ->). exists a3', a4'. reflexivity.
    + destruct Hms as (a1' & a3' & a4' & ->). exists a1', (Z_to_bv 64 34), a3', a4'. reflexivity.
Qed.
