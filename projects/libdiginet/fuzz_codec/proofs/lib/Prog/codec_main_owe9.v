(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 263 of its 284 lines of code are new or changed and 123 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_agree
  codec_main_inv codec_main_oweb_lib codec_main_owe910_lib memcpy_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** Segment OWE9 of the walk of LLVMFuzzerTestOneInput in the plain image: owe()'s SCRIBBLE case
    (fuzz_codec.c:211-218; 0x1443c-0x144f8). *)

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Ltac br_not := first [ if_false | (let E := fresh "E" in if_cases E; [ zify_cond E; exfalso; lia | ]) ].
Ltac br_yes := first [ if_true | (let E := fresh "E" in if_cases E; [ | zify_cond E; exfalso; lia ]) ].

(** ---- owe()'s SCRIBBLE case (fuzz_codec.c:211-218) ---- *)

Lemma owe9_rng_a : forall d a b c delta bytes n, 0x7f < a -> fst (owe_spec 9 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  replace (0x7f <? a) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma owe9_rng_b : forall d a b c delta bytes n, seven_bit (firstn (Z.to_nat (d_chars d)) bytes) = false ->
  fst (owe_spec 9 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  rewrite H. cbn [negb]. rewrite orb_true_r. reflexivity.
Qed.

Lemma owe9_ok : forall d a b c delta bytes n, a <= 0x7f -> seven_bit (firstn (Z.to_nat (d_chars d)) bytes) = true ->
  owe_spec 9 (Some d) a b c delta bytes n =
  (0, (fst (owe_sx (d_dev d) 0x40 ([u8 a; 0] ++ firstn (Z.to_nat (d_chars d)) bytes)), KEY 7 a,
       snd (owe_sx (d_dev d) 0x40 ([u8 a; 0] ++ firstn (Z.to_nat (d_chars d)) bytes)))).
Proof.
  intros d a b c delta bytes n Ha H. unfold owe_spec. cbv beta iota zeta.
  replace (0x7f <? a) with false by (symmetry; apply Z.ltb_ge; lia). rewrite H. cbn [negb orb]. reflexivity.
Qed.

(** One turn of seven_bit's loop (0x14458-0x14468) on byte j of k.bytes: lb, bltz -> E_RANGE, a1 - 1, a0 + 1,
    bnez; the exit owes E_RANGE. *)
Ltac sb_loop j BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK :=
  let HR := fresh "HR" in
  pose proof (bytes_at_byte _ _ _ (Z.of_nat j) BY ltac:(rewrite LB; lia)) as HR;
  zstep; zstep; clear HR;
  let P := fresh "P" in
  if_cases P; rewrite lts_sxb in P;
  [ zstep;
    eapply (owe_err_tail _ _ HE CHK) with (rc := E_RANGE);
      [ exact HF | exact HRC | exact HRCk | | | | exact HWL | exact HWK | exact HWD | exact HC | exact FR0 | exact HFR ];
      [ unfold owe_k; rewrite HK; apply owe9_rng_b; apply (seven_bit_firstn_false _ _ j);
        [ vm_compute; lia | unfold zb; rewrite length_map, LB; lia
        | apply sb_neg_nth; try rewrite Nat2Z.id in P; exact P ]
      | unfold E_RANGE; lia
      | first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ]
  | try rewrite Nat2Z.id in P; zstep; zstep; zstep ].

Lemma codec_main_owe9 : S_owe9.
Proof.
  unfold S_owe9, owe_ok, st, body_regs.
  intros MC e fuel HE CHK ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops k od c rem tl m1
         HF HRC HK HOD HRCk HWR HWL HWK HWD HC FR HFR.
  replace (owe_pc 9) with 0x1443c by reflexivity.
  unfold memcpy_contract in MC.
  pose proof HRC as (_ & HPD & HRD & _ & _).
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _ & _ & HPB & _ & HDJ). unfold LLVM_CODEC_STACK in HLO.
  pose proof HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  pose proof (relro_of_fr e m1 HE HFR) as HRI.
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & Rby & Rn & _).
  assert (LB : length (k_bytes k) = 24%nat) by (unfold zb in Rlen; rewrite length_map in Rlen; exact Rlen).
  destruct od as [d|]; [| exfalso; destruct (HOD eq_refl) as [X | [X | X]]; discriminate X].
  destruct (desk_ro m1 (k_p k) (k_desk k) d HRI HPD) as (Hd & Dr & Hdv & np & pad & DK).
  unfold desk_cells in DK.
  unfold disj, RELRO_BASE, RELRO_LEN in HDJ.
  pose proof FR as FR0.
  destruct (body_cut e m1 k c rem tl FR) as (FA & BY & WB & FC). clear FR.
  rewrite HWR in FC.
  apply (rw_cells_split_at _ _ _ 11 80 tl [70;1;1;1;1;1;1;1;1;1;1]%nat) in FC; [| reflexivity | reflexivity].
  cbn [firstn skipn mk_CB_cells app] in FC.
  destruct Hd as [-> | ->].
  - cbv [c24 d_dev d_strips d_chars d_counter] in DK.
    apply (rw_cells_split_at _ _ _ 5 24 (k_want k) [2;1;1;6;1;13]%nat) in FC; [| reflexivity | reflexivity].
    cbn [firstn skipn mk_CB_cells app] in FC.
    zstep. zstep. zstep.
    if_cases E1.
    + zify_cond E1.
      assert (Ha7 : 0x7f < k_a k) by (rewrite sx32_u in E1 by lia; destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
      zstep.
      eapply (owe_err_tail e fuel HE CHK) with (rc := E_RANGE);
        [ exact HF | exact HRC | exact HRCk | | | | exact HWL | exact HWK | exact HWD | exact HC | exact FR0 | exact HFR ].
      * unfold owe_k. rewrite HK. apply owe9_rng_a. lia.
      * unfold E_RANGE. lia.
      * first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
    + zify_cond E1.
      assert (Ha7 : k_a k <= 0x7f) by (rewrite sx32_u in E1 by lia; destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
      rewrite (sx32_small (k_a k)) by lia.
      zstep. zstep. zstep. zstep.
      br_not.
      sb_loop 0%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
      sb_loop 1%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
      sb_loop 2%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
      sb_loop 3%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_not.
      do 10 zstep.
      try clear FR0.
      assert (U112 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -112)) = bv_unsigned (e_sp e) + -112)
        by (apply unsigned_lit; lia).
      assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -344)) = bv_unsigned (e_sp e) + -344)
        by (apply unsigned_lit; lia).
      assert (U4 : bv_unsigned (Z_to_bv 64 4) = 4) by reflexivity.
      pose proof (bytes_at_firstn _ _ _ 4 BY) as B4.
      destruct (rw_cells_isolate _ _ _ 19 4 FC) as (Q1 & Q2 & Q3). clear FC.
      cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in Q1, Q2, Q3.
      fix_ofnat Q2. fix_ofnat Q3.
      replace (bv_unsigned (e_sp e) + -320 + 208) with (bv_unsigned (e_sp e) + -112) in Q2, Q3 by lia.
      zstep. zstep. zstep. zstep.
      call MC.
      { rewrite U344. exact B4. }
      { rewrite length_firstn, LB. reflexivity. }
      { rewrite U112. exact Q2. }
      { rewrite U344, U112. lia. }
      { assumption. }
      rewrite ?U112, ?U344 in *.
      match goal with T : rw_cells _ _ (bv_unsigned (e_sp e) + -112) _ |- _ =>
        rewrite U4 in T; change (Z.to_nat 4) with 4%nat in T; rename T into QT end.
      pose proof (rw_cells_join3n _ _ _ _ _ _ _ _ Q1 QT Q3 ltac:(cbn; lia) ltac:(cbn; lia)) as FC.
      clear Q1 QT Q3 POST. cbn [app] in FC.
      do 10 zstep.
      assert (U114 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -114)) = bv_unsigned (e_sp e) + -114)
        by (apply unsigned_lit; lia).
      assert (U236 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -236)) = bv_unsigned (e_sp e) + -236)
        by (apply unsigned_lit; lia).
      assert (U6 : bv_unsigned (Z_to_bv 64 6) = 6) by reflexivity.
      destruct (rw_cells_isolate _ _ _ 17 3 FC) as (_ & S2 & _).
      apply rw_cells_bytes_at in S2.
      cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in S2. fix_ofnat S2.
      replace (bv_unsigned (e_sp e) + -320 + 206) with (bv_unsigned (e_sp e) + -114) in S2 by lia.
      destruct (rw_cells_isolate _ _ _ 8 1 FC) as (Q1 & Q2 & Q3). clear FC.
      cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in Q1, Q2, Q3.
      fix_ofnat Q2. fix_ofnat Q3.
      replace (bv_unsigned (e_sp e) + -320 + 84) with (bv_unsigned (e_sp e) + -236) in Q2, Q3 by lia.
      call MC.
      { rewrite U114. exact S2. }
      { cbn [length]. rewrite length_app, length_firstn, LB. reflexivity. }
      { rewrite U236. exact Q2. }
      { rewrite U114, U236. lia. }
      { assumption. }
      rewrite ?U114, ?U236 in *.
      match goal with T : rw_cells _ _ (bv_unsigned (e_sp e) + -236) _ |- _ =>
        rewrite U6 in T; change (Z.to_nat 6) with 6%nat in T; rename T into QT end.
      pose proof (rw_cells_join3n _ _ _ _ _ _ _ _ Q1 QT Q3 ltac:(cbn; lia) ltac:(cbn; lia)) as FC.
      clear Q1 QT Q3 POST S2. cbn [app] in FC.
      do 2 zstep.
      replace (4 + (bv_unsigned (e_sp e) + -240)) with (bv_unsigned (e_sp e) + -236) by lia.
      do 10 zstep.
      pose proof (rw_cells_merge_at _ _ _ 5 6 FC) as FM. clear FC.
      cbn [firstn skipn cells_size csize Nat.add app] in FM.
      pose proof (rw_cells_merge_at _ _ _ 11 8 FM) as FM2. clear FM.
      cbn [firstn skipn cells_size csize Nat.add app] in FM2.
      pose proof (body_glue e _ k c rem _ _ _ _ _ _ FA BY WB LB FM2) as FB. clear FM2.
      set (BS := [0xf0; 0x13; u8 1; u8 64] ++ ([u8 (k_a k); 0] ++ firstn 4 (zb (k_bytes k))) ++ [0xf7]).
      assert (LBS : Z.of_nat (length BS) = 11)
        by (unfold BS; rewrite !length_app, length_firstn; unfold zb; rewrite length_map, LB; reflexivity).
      lazymatch type of FB with rw_cells _ _ _ (body_cells _ (set_owe _ _ ?W _ _ _) _ _ ?T) =>
        eapply (owe_ok_tail e fuel CHK) with (bs := BS) (key := KEY 7 (k_a k)) (dp := 1) (w := W) (tl := T) end;
        [ exact HF | exact HRC | exact HRCk | | | exact HC | | ].
      ++ unfold owe_k. rewrite HK. rewrite owe9_ok; [ unfold BS; reflexivity | lia | ].
        apply seven_bit_firstn_true.
        * change (Z.to_nat (d_chars c24)) with 4%nat. unfold zb. rewrite length_map, LB. lia.
        * change (Z.to_nat (d_chars c24)) with 4%nat. intros j Hj.
          assert (Ej : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat) by lia.
          destruct Ej as [-> | [-> | [-> | ->]]]; apply sb_pos_nth; assumption.
      ++ unfold BS. clear - LB Ha7.
        cbn [cells_bytes cbytes app]. rewrite le2_f013.
        revert LB. generalize (k_bytes k). intros kb Lkb.
        do 4 (destruct kb as [|? kb]; [discriminate|]).
        cbn [firstn zb bz map app length]. rewrite !b8_lit, !b8_u8, !b8_byte, b8_F7. reflexivity.
      ++ rewrite LBS. replace (KEY 7 (k_a k)) with (Z.lor (k_a k) 458752) by (rewrite (key_or 7 (k_a k)) by lia; reflexivity).
        exact FB.
      ++ refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
  - cbv [pc d_dev d_strips d_chars d_counter] in DK.
    apply (rw_cells_split_at _ _ _ 5 24 (k_want k) [2;1;1;10;1;9]%nat) in FC; [| reflexivity | reflexivity].
    cbn [firstn skipn mk_CB_cells app] in FC.
    zstep. zstep. zstep.
    if_cases E1.
    + zify_cond E1.
      assert (Ha7 : 0x7f < k_a k) by (rewrite sx32_u in E1 by lia; destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
      zstep.
      eapply (owe_err_tail e fuel HE CHK) with (rc := E_RANGE);
        [ exact HF | exact HRC | exact HRCk | | | | exact HWL | exact HWK | exact HWD | exact HC | exact FR0 | exact HFR ].
      * unfold owe_k. rewrite HK. apply owe9_rng_a. lia.
      * unfold E_RANGE. lia.
      * first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
    + zify_cond E1.
      assert (Ha7 : k_a k <= 0x7f) by (rewrite sx32_u in E1 by lia; destruct (Z.ltb_spec (k_a k) (2 ^ 31)); lia).
      rewrite (sx32_small (k_a k)) by lia.
      zstep. zstep. zstep. zstep.
      br_not.
      sb_loop 0%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
      sb_loop 1%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
      sb_loop 2%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
      sb_loop 3%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
      sb_loop 4%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
      sb_loop 5%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
      sb_loop 6%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
      sb_loop 7%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_not.
      do 10 zstep.
      try clear FR0.
      assert (U112 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -112)) = bv_unsigned (e_sp e) + -112)
        by (apply unsigned_lit; lia).
      assert (U344 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -344)) = bv_unsigned (e_sp e) + -344)
        by (apply unsigned_lit; lia).
      assert (U8 : bv_unsigned (Z_to_bv 64 8) = 8) by reflexivity.
      pose proof (bytes_at_firstn _ _ _ 8 BY) as B4.
      destruct (rw_cells_isolate _ _ _ 19 8 FC) as (Q1 & Q2 & Q3). clear FC.
      cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in Q1, Q2, Q3.
      fix_ofnat Q2. fix_ofnat Q3.
      replace (bv_unsigned (e_sp e) + -320 + 208) with (bv_unsigned (e_sp e) + -112) in Q2, Q3 by lia.
      zstep. zstep. zstep. zstep.
      call MC.
      { rewrite U344. exact B4. }
      { rewrite length_firstn, LB. reflexivity. }
      { rewrite U112. exact Q2. }
      { rewrite U344, U112. lia. }
      { assumption. }
      rewrite ?U112, ?U344 in *.
      match goal with T : rw_cells _ _ (bv_unsigned (e_sp e) + -112) _ |- _ =>
        rewrite U8 in T; change (Z.to_nat 8) with 8%nat in T; rename T into QT end.
      pose proof (rw_cells_join3n _ _ _ _ _ _ _ _ Q1 QT Q3 ltac:(cbn; lia) ltac:(cbn; lia)) as FC.
      clear Q1 QT Q3 POST. cbn [app] in FC.
      do 10 zstep.
      assert (U114 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -114)) = bv_unsigned (e_sp e) + -114)
        by (apply unsigned_lit; lia).
      assert (U236 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -236)) = bv_unsigned (e_sp e) + -236)
        by (apply unsigned_lit; lia).
      assert (U10 : bv_unsigned (Z_to_bv 64 10) = 10) by reflexivity.
      destruct (rw_cells_isolate _ _ _ 17 3 FC) as (_ & S2 & _).
      apply rw_cells_bytes_at in S2.
      cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in S2. fix_ofnat S2.
      replace (bv_unsigned (e_sp e) + -320 + 206) with (bv_unsigned (e_sp e) + -114) in S2 by lia.
      destruct (rw_cells_isolate _ _ _ 8 1 FC) as (Q1 & Q2 & Q3). clear FC.
      cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in Q1, Q2, Q3.
      fix_ofnat Q2. fix_ofnat Q3.
      replace (bv_unsigned (e_sp e) + -320 + 84) with (bv_unsigned (e_sp e) + -236) in Q2, Q3 by lia.
      call MC.
      { rewrite U114. exact S2. }
      { cbn [length]. rewrite length_app, length_firstn, LB. reflexivity. }
      { rewrite U236. exact Q2. }
      { rewrite U114, U236. lia. }
      { assumption. }
      rewrite ?U114, ?U236 in *.
      match goal with T : rw_cells _ _ (bv_unsigned (e_sp e) + -236) _ |- _ =>
        rewrite U10 in T; change (Z.to_nat 10) with 10%nat in T; rename T into QT end.
      pose proof (rw_cells_join3n _ _ _ _ _ _ _ _ Q1 QT Q3 ltac:(cbn; lia) ltac:(cbn; lia)) as FC.
      clear Q1 QT Q3 POST S2. cbn [app] in FC.
      do 2 zstep.
      replace (8 + (bv_unsigned (e_sp e) + -240)) with (bv_unsigned (e_sp e) + -232) by lia.
      do 10 zstep.
      pose proof (rw_cells_merge_at _ _ _ 5 6 FC) as FM. clear FC.
      cbn [firstn skipn cells_size csize Nat.add app] in FM.
      pose proof (rw_cells_merge_at _ _ _ 11 4 FM) as FM2. clear FM.
      cbn [firstn skipn cells_size csize Nat.add app] in FM2.
      pose proof (body_glue e _ k c rem _ _ _ _ _ _ FA BY WB LB FM2) as FB. clear FM2.
      set (BS := [0xf0; 0x13; u8 0; u8 64] ++ ([u8 (k_a k); 0] ++ firstn 8 (zb (k_bytes k))) ++ [0xf7]).
      assert (LBS : Z.of_nat (length BS) = 15)
        by (unfold BS; rewrite !length_app, length_firstn; unfold zb; rewrite length_map, LB; reflexivity).
      lazymatch type of FB with rw_cells _ _ _ (body_cells _ (set_owe _ _ ?W _ _ _) _ _ ?T) =>
        eapply (owe_ok_tail e fuel CHK) with (bs := BS) (key := KEY 7 (k_a k)) (dp := 1) (w := W) (tl := T) end;
        [ exact HF | exact HRC | exact HRCk | | | exact HC | | ].
      ++ unfold owe_k. rewrite HK. rewrite owe9_ok; [ unfold BS; reflexivity | lia | ].
        apply seven_bit_firstn_true.
        * change (Z.to_nat (d_chars pc)) with 8%nat. unfold zb. rewrite length_map, LB. lia.
        * change (Z.to_nat (d_chars pc)) with 8%nat. intros j Hj.
          assert (Ej : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat \/ j = 4%nat \/ j = 5%nat \/ j = 6%nat \/ j = 7%nat) by lia.
          destruct Ej as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; apply sb_pos_nth; assumption.
      ++ unfold BS. clear - LB Ha7.
        cbn [cells_bytes cbytes app]. rewrite le2_f013.
        revert LB. generalize (k_bytes k). intros kb Lkb.
        do 8 (destruct kb as [|? kb]; [discriminate|]).
        cbn [firstn zb bz map app length]. rewrite !b8_lit, !b8_u8, !b8_byte, b8_F7. reflexivity.
      ++ rewrite LBS. replace (KEY 7 (k_a k)) with (Z.lor (k_a k) 458752) by (rewrite (key_or 7 (k_a k)) by lia; reflexivity).
        exact FB.
      ++ refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.
