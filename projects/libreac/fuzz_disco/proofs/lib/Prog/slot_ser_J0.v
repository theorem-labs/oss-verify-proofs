From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_inv slot_lib printf_facts_c slot_ser_ws.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import slot_ser_tokb.
Import ListNotations.
Open Scope Z_scope.

Lemma zbv_eq : forall a c, a mod 2 ^ 64 = c mod 2 ^ 64 -> Z_to_bv 64 a = Z_to_bv 64 c.
Proof.
  intros a c H. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  exact H.
Qed.

Lemma neg_lit : forall z, Z_to_bv 64 (0 - bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 64 (- z).
Proof.
  intros z. apply zbv_eq. rewrite unsigned_lit_wrap. rewrite Zminus_mod_idemp_r. f_equal; lia.
Qed.

Lemma at_byte_true : forall B i c, at_byte B i c = true -> i < jlen B /\ jbyte B i = c.
Proof.
  intros B i c H. unfold at_byte in H. apply andb_true_iff in H as [H1 H2].
  apply Z.ltb_lt in H1. apply Z.eqb_eq in H2. split; assumption.
Qed.

Lemma js_rng : forall B i j k s l, jscalar B i = Some (j, k, s, l) -> i < jlen B /\ i <= j <= jlen B.
Proof.
  intros B i j k s l H. unfold jscalar in H.
  destruct (jlen B <=? i) eqn:E1; cbv beta iota in H; [discriminate|]. apply Z.leb_gt in E1.
  split; [exact E1|].
  destruct (jbyte B i =? 34) eqn:E2; cbv beta iota in H.
  - apply jstr_bnd in H. destruct H as (jc & Hjc & Heq). injection Heq; intros; subst. lia.
  - destruct (jlit B i jlit_words) as [t|] eqn:E3; cbv beta iota in H.
    + injection H; intros; subst. apply jlit_bnd in E3. destruct E3 as (n & Hn & Heq).
      injection Heq; intros; subst. lia.
    + apply jnum_bnd in H. destruct H as (j3 & Hj3 & Heq). injection Heq; intros; subst. lia.
Qed.

Lemma jr_unfold : forall B count os, json_read B 9 = Some (count, os) ->
  at_byte B (json_ws B 0) 91 = true /\
  ((at_byte B (json_ws B (json_ws B 0 + 1)) 93 = true /\ json_ws B (json_ws B (json_ws B 0 + 1) + 1) = jlen B /\
    count = 0 /\ os = []) \/
   (at_byte B (json_ws B (json_ws B 0 + 1)) 93 = false /\
    json_objs B (json_ws B (json_ws B 0 + 1)) 0 9 [] (length B) = Some (count, os))).
Proof.
  intros B count os H. unfold json_read in H. cbv zeta in H.
  destruct (at_byte B (json_ws B 0) 91) eqn:E1; cbn [negb] in H; cbv iota in H; [|discriminate].
  split; [reflexivity|].
  destruct (at_byte B (json_ws B (json_ws B 0 + 1)) 93) eqn:E2; cbv iota in H.
  - left. destruct (json_ws B (json_ws B (json_ws B 0 + 1) + 1) =? jlen B) eqn:E3; cbv iota in H; [|discriminate].
    apply Z.eqb_eq in E3. injection H; intros; subst. tauto.
  - right. tauto.
Qed.

Lemma jobjs_first : forall B i count max acc f r, json_objs B i count max acc f = Some r -> at_byte B i 123 = true.
Proof.
  intros B i count max acc [|f] r H; cbn [json_objs] in H; [discriminate|].
  destruct (at_byte B i 123); [reflexivity|discriminate].
Qed.

Lemma slot_R10 : forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (b count : Z) (B : list Z) (os : list jobj),
  s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 b -> s4 = Z_to_bv 64 (jlen B) ->
  0 < b -> b + jlen B + 1 < 2 ^ 63 ->
  Forall (fun c => 0 <= c < 256) B -> bytes_at rsegs m b (pf_bytes (B ++ [0])) ->
  json_read B 9 = Some (count, os) ->
  evt rsegs
    (fun ms' =>
       (exists a0' a1' a2' a3' s10' : word, count = 0 /\ os = [] /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                        s2 s3 s4 s5 (Z_to_bv 64 0) s7 s8 s9 s10' s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x140bc) fc None m (seg_rom rsegs)) \/
       (exists (a0' a1' a2' a3' : word) (i1 : Z),
          0 <= i1 /\ json_objs B i1 0 9 [] (length B) = Some (count, os) /\
          ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2' a3' a4 a5 a6 a7
                        s2 s3 s4 s5 s6 s7 s8 s9 (Z_to_bv 64 i1) s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1392c) fc None m (seg_rom rsegs)))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x13660) fc None m (seg_rom rsegs)).
Proof.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m b count B os
    E0 E2 E3 E4 Hb HbB FB BB JR.
  destruct (jr_unfold B count os JR) as [A0 JR'].
  set (i0 := json_ws B 0) in *. set (i1 := json_ws B (i0 + 1)) in *.
  pose proof (ws_ge B 0 ltac:(lia)) as G0. fold i0 in G0.
  pose proof (ws_ge B (i0 + 1) ltac:(lia)) as G1. fold i1 in G1.
  destruct (at_byte_true B i0 91 A0) as [L0 C0].
  assert (L1 : i1 < jlen B).
  { destruct JR' as [(A1 & _)|(_ & JO)]; [exact (proj1 (at_byte_true B i1 93 A1))|].
    exact (proj1 (at_byte_true B i1 123 (jobjs_first _ _ _ _ _ _ _ JO))). }
  assert (L01 : i0 + 1 < jlen B) by (apply (ws_lt B (i0 + 1)); [lia | exact L1]).
  subst s0 s2 s3 s4.
  step. step. step.
  eapply evt_cut.
  { eapply (ws_L5 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b 0 B);
      first [reflexivity | (f_equal; lia) | lia | assumption]. }
  intros ms' [a3' E]. subst ms'. fold i0.
  step. rewrite ltu_lit by lia. replace (i0 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
  step. step. rewrite C0, eqb_lit by lia. rewrite Z.eqb_refl. cbn [negb]. cbv iota.
  step. step. rewrite ltu_lit by lia. replace (i0 + 1 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. cbv iota.
  step.
  eapply evt_cut.
  { eapply (ws_L6 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b (i0 + 1) B);
      first [reflexivity | (f_equal; lia) | (rewrite neg_lit; f_equal; lia) | (rewrite unsigned_lit by lia; f_equal; lia)
            | lia | assumption]. }
  intros ms' [a3'' E]. subst ms'. fold i1.
  step. rewrite !neg_lit. replace (- - i1) with i1 by lia.
  step. rewrite ltu_lit by lia. replace (i1 <? jlen B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb]. cbv iota.
  pose proof (ws_rd m b B i1 BB ltac:(lia)) as RD1. pose proof (ws_byte B i1 FB) as HC1.
  step. step. rewrite ws_zxb by lia. step. step. rewrite eqb_lit by lia.
  destruct JR' as [(A1 & W2 & Ec & Eo)|(A1 & JO)].
  - destruct (at_byte_true B i1 93 A1) as [_ C1]. rewrite C1, Z.eqb_refl. cbn [negb]. cbv iota.
    step. step. rewrite ltu_lit by lia.
    destruct (Z.ltb_spec (i1 + 1) (jlen B)) as [Lt|Ge]; cbn [negb]; cbv iota.
    + eapply evt_cut.
      { eapply (ws_L7 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m b (i1 + 1) B);
          first [reflexivity | lia | assumption]. }
      intros ms' [a0x E]. subst ms'. rewrite W2.
      step. step. rewrite !Z.lxor_nilpotent.
      replace (v_sltiu (Z_to_bv 64 0) 1) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
      step. step. apply evt_done. left. do 5 eexists. split; [exact Ec|]. split; [exact Eo|]. reflexivity.
    + replace (i1 + 1) with (jlen B) by lia.
      step. step. rewrite !Z.lxor_nilpotent.
      replace (v_sltiu (Z_to_bv 64 0) 1) with (Z_to_bv 64 1) by (vm_compute; reflexivity).
      step. step. apply evt_done. left. do 5 eexists. split; [exact Ec|]. split; [exact Eo|]. reflexivity.
  - assert (C1 : jbyte B i1 <> 93).
    { intro C. unfold at_byte in A1. rewrite (proj2 (Z.ltb_lt _ _) L1), C in A1. discriminate. }
    rewrite (proj2 (Z.eqb_neq _ _) C1). cbn [negb]. cbv iota.
    apply evt_done. right. do 4 eexists. exists i1. split; [lia|]. split; [exact JO|]. reflexivity.
Qed.
