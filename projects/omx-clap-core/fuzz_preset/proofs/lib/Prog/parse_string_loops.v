From Stdlib Require Import ZArith List Lia Bool Arith.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjGrammar.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame Tac Bytes Step ZBridge.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require hex4_c hex4.
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

Lemma ps_scan_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (text len x : Z) (tb : list byte),
  a0 = Z_to_bv 64 (text + len) -> a1 = Z_to_bv 64 34 -> a2 = Z_to_bv 64 x ->
  bytes_at rsegs m text tb -> Z.of_nat (length tb) = len -> text + len < 2 ^ 62 -> text <= x < text + len ->
  evt rsegs
    (fun ms' => match scan (rest_at tb text x) with
       | Some Q => exists a3' : word,
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 (Z_to_bv 64 (x + Z.of_nat Q)) a3' a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1665c) fc None m (seg_rom rsegs)
       | None => exists a2' a3' : word,
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2' a3' a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x168d8) fc None m (seg_rom rsegs)
       end)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1663c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m text len x tb
    E0 E1 E2 HB HL Hend Hx.
  pose proof (bytes_at_bound rsegs m text tb HB) as [Ht _].
  subst a0 a1.
  remember (Z.to_nat (text + len - x)) as n eqn:Hn.
  revert x a2 a3 E2 Hx Hn.
  induction n as [n IH] using lt_wf_ind.
  intros x a2 a3 E2 Hx Hn. subst a2.
  destruct (nth_error tb (Z.to_nat (x - text))) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
  pose proof (psl_read m text tb x c HB ltac:(lia) Hc) as RD.
  pose proof (psl_rest_cons tb text x c ltac:(lia) Hc) as HR.
  assert (HZ : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  step. step.
  if_cases HC1.
  - cond_fact HC1. rewrite Z.mod_small in HC1 by lia.
    apply evt_done. cbv beta. rewrite HR, HC1, psl_scan_q. cbv beta iota.
    replace (x + Z.of_nat 0) with x by lia. eexists. reflexivity.
  - cond_fact HC1. rewrite Z.mod_small in HC1 by lia.
    step. step. step. step. step.
    rewrite (psl_seqz c HZ).
    destruct (Z.eqb_spec (bv_unsigned c) 92) as [B|B].
    + replace (1 + x + 1) with (x + 2) by lia.
      rewrite (psl_ltu (x + 2) (text + len)) by lia.
      rewrite HR, B.
      destruct (Z.ltb_spec (x + 2) (text + len)) as [L|L]; cbv iota.
      * destruct (nth_error tb (Z.to_nat (x + 1 - text))) as [e|] eqn:He; [|apply nth_error_None in He; lia].
        rewrite (psl_rest_cons tb text (x + 1) e ltac:(lia) He), scan_bs.
        replace (x + 1 + 1) with (x + 2) by lia.
        eapply evt_mono.
        { apply (IH (Z.to_nat (text + len - (x + 2))) ltac:(lia) (x + 2) _ (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -92)) 1) eq_refl ltac:(lia) eq_refl). }
        intros ms' Hms. cbv beta in Hms |- *.
        destruct (scan (rest_at tb text (x + 2))) as [Q|]; cbn [option_map].
        -- destruct Hms as [a3' ->]. exists a3'. replace (x + Z.of_nat (S (S Q))) with (x + 2 + Z.of_nat Q) by lia. reflexivity.
        -- exact Hms.
      * step. apply evt_done. cbv beta.
        destruct (Z.ltb_spec (x + 1) (text + len)) as [L1|L1].
        -- destruct (nth_error tb (Z.to_nat (x + 1 - text))) as [e|] eqn:He; [|apply nth_error_None in He; lia].
           rewrite (psl_rest_cons tb text (x + 1) e ltac:(lia) He), scan_bs.
           rewrite (psl_rest_end tb text (x + 1 + 1)) by lia.
           cbn [scan option_map]. do 2 eexists. reflexivity.
        -- rewrite (psl_rest_end tb text (x + 1)) by lia.
           rewrite psl_scan_bs1. cbv beta iota. do 2 eexists. reflexivity.
    + replace (0 + x + 1) with (x + 1) by lia.
      rewrite (psl_ltu (x + 1) (text + len)) by lia.
      rewrite HR, (scan_ndq (bv_unsigned c) _ HC1 B).
      destruct (Z.ltb_spec (x + 1) (text + len)) as [L|L]; cbv iota.
      * eapply evt_mono.
        { apply (IH (Z.to_nat (text + len - (x + 1))) ltac:(lia) (x + 1) _ (v_sltiu (Z_to_bv 64 (bv_unsigned (zxb c) + -92)) 1) eq_refl ltac:(lia) eq_refl). }
        intros ms' Hms. cbv beta in Hms |- *.
        destruct (scan (rest_at tb text (x + 1))) as [Q|]; cbn [option_map].
        -- destruct Hms as [a3' ->]. exists a3'. replace (x + Z.of_nat (S Q)) with (x + 1 + Z.of_nat Q) by lia. reflexivity.
        -- exact Hms.
      * step. apply evt_done. cbv beta.
        rewrite (psl_rest_end tb text (x + 1)) by lia.
        cbn [scan option_map]. do 2 eexists. reflexivity.
Qed.

Lemma ps_scan : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (text len s : Z) (tb : list byte),
  a0 = Z_to_bv 64 (text + len) -> s8 = Z_to_bv 64 s ->
  bytes_at rsegs m text tb -> Z.of_nat (length tb) = len -> text + len < 2 ^ 62 -> text <= s <= text + len ->
  evt rsegs
    (fun ms' => match scan (rest_at tb text s) with
       | Some Q => exists a3' : word,
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 34) (Z_to_bv 64 (s + Z.of_nat Q)) a3' a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1665c) fc None m (seg_rom rsegs)
       | None => exists a1' a2' a3' : word,
           ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4 a5 a6 a7
                         s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x168d8) fc None m (seg_rom rsegs)
       end)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x16630) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m text len s tb
    E0 E8 HB HL Hend Hs.
  pose proof (bytes_at_bound rsegs m text tb HB) as [Ht _].
  subst a0 s8.
  step.
  if_cases HC1.
  - cond_fact HC1.
    apply evt_done. cbv beta.
    rewrite (psl_rest_end tb text s) by lia. cbn [scan].
    do 3 eexists. reflexivity.
  - cond_fact HC1.
    step. step.
    eapply evt_mono.
    { apply (ps_scan_loop ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (text + len)) (Z_to_bv 64 34) (Z_to_bv 64 s) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 (Z_to_bv 64 s) s9 s10 s11 t3 t4 t5 t6 F fc m text len s tb
               eq_refl eq_refl eq_refl HB HL Hend ltac:(lia)). }
    intros ms' Hms. cbv beta in Hms |- *.
    destruct (scan (rest_at tb text s)) as [Q|].
    + destruct Hms as [a3' ->]. exists a3'. reflexivity.
    + destruct Hms as (a2' & a3' & ->). exists (Z_to_bv 64 34), a2', a3'. reflexivity.
Qed.

Lemma psl_acc : forall v z K, 0 <= v < 2 ^ 12 -> 0 <= K + z < 16 -> 0 <= z < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (K + bv_unsigned (Z_to_bv 64 z))))
                    (bv_unsigned (Z_to_bv 64 (bv_swrap 32 (Z.shiftl (bv_unsigned (Z_to_bv 64 v)) 4))))) =
  Z_to_bv 64 (16 * v + (K + z)).
Proof.
  intros v z K Hv Hk Hz.
  rewrite (unsigned_lit z) by lia. rewrite (unsigned_lit v) by lia. rewrite (unsigned_lit (K + z)) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite bv_swrap_small by (change (bv_half_modulus 32) with (2 ^ 31); change (2 ^ 4) with 16; lia).
  rewrite (unsigned_lit (v * 2 ^ 4)) by (change (2 ^ 4) with 16; lia).
  rewrite hex4.hex4_lor_low4 by lia. reflexivity.
Qed.

Local Ltac hexval_solve :=
  unfold hex4_c.hexval;
  repeat match goal with |- context [Z.leb ?a ?b] => destruct (Z.leb_spec a b) end; cbn [andb];
  first [ reflexivity | f_equal; lia | exfalso; lia ].

Lemma psl_hex_turn : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Q : machine_state -> Prop) (P v n : Z) (c : byte),
  0 <= P < 2 ^ 64 -> 0 <= v < 2 ^ 12 -> 1 <= n <= 4 ->
  ov_read_bytes rsegs m (wa P) 1 = Some [c] ->
  (forall d, hex4_c.hexval c = Some d -> forall x1 x2 x3 x4 y3 y10 : word,
     x1 = Z_to_bv 64 (n - 1) -> y3 = Z_to_bv 64 (16 * v + d) -> y10 = Z_to_bv 64 (P + 1) ->
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 x1 x2 x3 x4 a5 a6 a7 s2 y3 s4 s5 s6 s7 s8
                          (Z_to_bv 64 10) y10 (Z_to_bv 64 6) t3 t4 t5 t6) F (Z_to_bv 64 0x1677c) fc None m (seg_rom rsegs))) ->
  (hex4_c.hexval c = None -> forall x2 x3 x4 : word,
     evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) x2 x3 x4 a5 a6 a7 s2 (Z_to_bv 64 v) s4 s5 s6 s7 s8
                          (Z_to_bv 64 10) (Z_to_bv 64 P) (Z_to_bv 64 6) t3 t4 t5 t6) F (Z_to_bv 64 0x168d0) fc None m (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 v) s4 s5 s6 s7 s8
                       (Z_to_bv 64 10) (Z_to_bv 64 P) (Z_to_bv 64 6) t3 t4 t5 t6) F (Z_to_bv 64 0x16734) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a2 a3 a4 a5 a6 a7 s2 s4 s5 s6 s7 s8 t3 t4 t5 t6 F fc m Q P v n c HP HV HN RD KS KF.
  assert (HZ : 0 <= bv_unsigned c < 256) by (pose proof (bv_unsigned_in_range 8 c) as H; unfold bv_modulus in H; exact H).
  step. step. step.
  if_cases HC1.
  - cond_fact HC1.
    assert (N1 : ~ (48 <= bv_unsigned c <= 57)) by (Z.div_mod_to_equations; lia). clear HC1.
    step. step.
    if_cases HC2.
    + cond_fact HC2.
      assert (N2 : ~ (97 <= bv_unsigned c <= 102)) by (Z.div_mod_to_equations; lia). clear HC2.
      step. step. step.
      if_cases HC3.
      * cond_fact HC3.
        assert (N3 : ~ (65 <= bv_unsigned c <= 70)) by (Z.div_mod_to_equations; lia). clear HC3.
        eapply KF. hexval_solve.
      * cond_fact HC3.
        assert (D : 65 <= bv_unsigned c <= 70) by (Z.div_mod_to_equations; lia). clear HC3.
        step. step. step. step. step. step.
        unfold zxb.
        eapply (KS (-55 + bv_unsigned c)); [ hexval_solve | f_equal; lia | apply psl_acc; lia | reflexivity ].
    + cond_fact HC2.
      assert (D : 97 <= bv_unsigned c <= 102) by (Z.div_mod_to_equations; lia). clear HC2.
      step. step. step. step. step. step. step.
      unfold zxb.
      eapply (KS (-87 + bv_unsigned c)); [ hexval_solve | f_equal; lia | apply psl_acc; lia | reflexivity ].
  - cond_fact HC1.
    assert (D : 48 <= bv_unsigned c <= 57) by (Z.div_mod_to_equations; lia). clear HC1.
    step. step. step. step. step. step. step.
    unfold zxb.
    eapply (KS (-48 + bv_unsigned c)); [ hexval_solve | f_equal; lia | apply psl_acc; lia | reflexivity ].
Qed.

Local Ltac rd R :=
  lazymatch type of R with
  | ov_read_bytes _ _ (wa ?A) _ = _ =>
      lazymatch goal with |- ov_read_bytes _ _ (wa ?a) _ = _ => replace a with A by lia; exact R end
  end.

Local Ltac hex_none :=
  apply evt_done; cbv beta; do 6 eexists;
  cbv beta iota delta [hex4_c.hex4];
  repeat match goal with H : hex4_c.hexval _ = _ |- _ => rewrite H; clear H end;
  cbv beta iota; reflexivity.

Lemma ps_hex_loop : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (P : Z) (b0 b1 b2 b3 : byte),
  s9 = Z_to_bv 64 10 -> s10 = Z_to_bv 64 P -> s11 = Z_to_bv 64 6 -> bytes_at rsegs m P [b0; b1; b2; b3] ->
  evt rsegs (fun ms' => exists (a1' a2' a3' a4' s3' s10' : word),
     match hex4_c.hex4 [b0; b1; b2; b3] with
     | Some h => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5 a6 a7 s2 (Z_to_bv 64 h) s4 s5 s6 s7 s8 s9
                               (Z_to_bv 64 (P + 4)) s11 t3 t4 t5 t6) F (Z_to_bv 64 0x16780) fc None m (seg_rom rsegs)
     | None => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3' a4' a5 a6 a7 s2 s3' s4 s5 s6 s7 s8 s9 s10' s11
                             t3 t4 t5 t6) F (Z_to_bv 64 0x168d0) fc None m (seg_rom rsegs)
     end)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1672c) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m P b0 b1 b2 b3
    E9 E10 E11 HB.
  subst s9 s10 s11.
  pose proof HB as (HPl & HPh & _). cbn [length Z.of_nat Pos.of_succ_nat Pos.succ] in HPh.
  assert (R0 : ov_read_bytes rsegs m (wa P) 1 = Some [b0]).
  { rewrite <- (Z.add_0_r P) at 1. rewrite (bytes_at_read rsegs m P _ 0 1 HB) by (cbn; lia). reflexivity. }
  assert (R1 : ov_read_bytes rsegs m (wa (P + 1)) 1 = Some [b1]).
  { rewrite (bytes_at_read rsegs m P _ 1 1 HB) by (cbn; lia). reflexivity. }
  assert (R2 : ov_read_bytes rsegs m (wa (P + 2)) 1 = Some [b2]).
  { rewrite (bytes_at_read rsegs m P _ 2 1 HB) by (cbn; lia). reflexivity. }
  assert (R3 : ov_read_bytes rsegs m (wa (P + 3)) 1 = Some [b3]).
  { rewrite (bytes_at_read rsegs m P _ 3 1 HB) by (cbn; lia). reflexivity. }
  step. step.
  eapply psl_hex_turn; [ lia | lia | lia | rd R0 | intros d0 H0 ? ? ? ? ? ? -> -> -> | intros H0 ? ? ? ].
  2: hex_none.
  pose proof (hex4.hexval_range _ _ H0) as G0.
  step. if_true.
  eapply psl_hex_turn; [ lia | lia | lia | rd R1 | intros d1 H1 ? ? ? ? ? ? -> -> -> | intros H1 ? ? ? ].
  2: hex_none.
  pose proof (hex4.hexval_range _ _ H1) as G1.
  step. if_true.
  eapply psl_hex_turn; [ lia | lia | lia | rd R2 | intros d2 H2 ? ? ? ? ? ? -> -> -> | intros H2 ? ? ? ].
  2: hex_none.
  pose proof (hex4.hexval_range _ _ H2) as G2.
  step. if_true.
  eapply psl_hex_turn; [ lia | lia | lia | rd R3 | intros d3 H3 ? ? ? ? ? ? -> -> -> | intros H3 ? ? ? ].
  2: hex_none.
  pose proof (hex4.hexval_range _ _ H3) as G3.
  step. if_false.
  match goal with |- context [Z_to_bv 64 (16 * ?w + d3)] =>
    replace (16 * w + d3) with (4096 * d0 + 256 * d1 + 16 * d2 + d3) by lia end.
  replace (P + 1 + 1 + 1 + 1) with (P + 4) by lia.
  apply evt_done; cbv beta. do 4 eexists. exists s3, s3.
  cbv beta iota delta [hex4_c.hex4]. rewrite H0, H1, H2, H3. cbv beta iota.
  reflexivity.
Qed.
