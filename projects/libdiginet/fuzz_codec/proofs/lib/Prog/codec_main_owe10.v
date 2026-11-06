(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColA/W_set0A.v, with its module paths and module names changed; 163 of its 184 lines of code are new or changed and 123 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib Require Import Img0.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Spec Require Import DgnSpec DgnLib.
From OSSVerify.Proofs.libdiginet.fuzz_codec.lib.Prog Require Import codec_owe codec_cells codec_img codec_agree
  codec_main_inv codec_main_oweb_lib codec_main_owe910_lib memcpy_c LLVMFuzzerTestOneInput_c.
Import ListNotations.
Open Scope Z_scope.

(** Segment OWE10 of the walk of LLVMFuzzerTestOneInput in the plain image: owe()'s COUNTER case
    (fuzz_codec.c:221-229; 0x1472c-0x147ec and the key store 0x14534-0x14538). *)

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

Lemma owe10_rng_b : forall d a b c delta bytes n, 0x7f < b -> fst (owe_spec 10 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  replace (0x7f <? b) with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
Qed.

Lemma owe10_rng_s : forall d a b c delta bytes n, seven_bit (firstn 8 bytes) = false ->
  fst (owe_spec 10 (Some d) a b c delta bytes n) = E_RANGE.
Proof.
  intros d a b c delta bytes n H. unfold owe_spec. cbv beta iota zeta.
  rewrite H. cbn [negb]. rewrite orb_true_r. reflexivity.
Qed.

Lemma owe10_ok : forall d a b c delta bytes n, b <= 0x7f -> seven_bit (firstn 8 bytes) = true ->
  owe_spec 10 (Some d) a b c delta bytes n =
  (0, ([0xf0; 0x13; u8 (d_dev d); u8 0x30] ++ ([d_counter d; u8 b] ++ rev (firstn 8 bytes)) ++ [0xf7],
       KEY 6 (d_counter d), 1)).
Proof.
  intros d a b c delta bytes n Hb H. unfold owe_spec. cbv beta iota zeta.
  replace (0x7f <? b) with false by (symmetry; apply Z.ltb_ge; lia). rewrite H. cbn [negb orb]. reflexivity.
Qed.

(** One turn of seven_bit's loop (0x14740-0x14750) on byte j of k.bytes; the exit owes E_RANGE. *)
Ltac sb_loop10 j BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK :=
  let HR := fresh "HR" in
  pose proof (bytes_at_byte _ _ _ (Z.of_nat j) BY ltac:(rewrite LB; lia)) as HR;
  zstep; zstep; clear HR;
  let P := fresh "P" in
  if_cases P; rewrite lts_sxb in P;
  [ zstep;
    eapply (owe_err_tail _ _ HE CHK) with (rc := E_RANGE);
      [ exact HF | exact HRC | exact HRCk | | | | exact HWL | exact HWK | exact HWD | exact HC | exact FR0 | exact HFR ];
      [ unfold owe_k; rewrite HK; apply owe10_rng_s; apply (seven_bit_firstn_false _ _ j);
        [ lia | unfold zb; rewrite length_map, LB; lia
        | apply sb_neg_nth; try rewrite Nat2Z.id in P; exact P ]
      | unfold E_RANGE; lia
      | first [ reflexivity | apply bv_eq; vm_compute; reflexivity ] ]
  | try rewrite Nat2Z.id in P; zstep; zstep; zstep ].

(** One turn of the reversal loop (0x1478c-0x1479c): pl[2 + j] = bytes[7 - j]. *)
Ltac rev_loop j BY LB :=
  let HR := fresh "HR" in
  pose proof (bytes_at_byte _ _ _ (7 - j) BY ltac:(rewrite LB; lia)) as HR;
  zstep; clear HR; zstep; zstep; zstep; zstep.

Lemma codec_main_owe10 : S_owe10.
Proof.
  unfold S_owe10, owe_ok, st, body_regs.
  intros MC e fuel HE CHK ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s5' s8' t3' t4' t5' t6' ops k od c rem tl m1
         HF HRC HK HOD HRCk HWR HWL HWK HWD HC FR HFR.
  replace (owe_pc 10) with 0x1472c by reflexivity.
  unfold memcpy_contract in MC.
  pose proof HRC as (_ & HPD & HRD & _ & _).
  pose proof (bv_unsigned_in_range 64 (e_sp e)) as Rsp. unfold bv_modulus in Rsp.
  pose proof HE as (_ & _ & _ & HLO & _ & _ & HPB & _ & HDJ). unfold LLVM_CODEC_STACK in HLO.
  pose proof HFR as (SV & ST & MU & WM & HMI). unfold LLVM_CODEC_STACK in MU.
  pose proof ST as [Hlo0 _].
  pose proof (relro_of_fr e m1 HE HFR) as HRI.
  pose proof HRD as (Ra & Rb & Rc & Rdl & Rlen & Rby & Rn & _ & Rb8 & _). specialize (Rb8 HK).
  assert (LB : length (k_bytes k) = 24%nat) by (unfold zb in Rlen; rewrite length_map in Rlen; exact Rlen).
  destruct od as [d|]; [| exfalso; destruct (HOD eq_refl) as [X | [X | X]]; discriminate X].
  destruct (desk_ro m1 (k_p k) (k_desk k) d HRI HPD) as (Hd & Dr & Hdv & np & pad & DK).
  pose proof Dr as (Ddev & Dstr & Dch & Dctr).
  assert (Rdev : 0 <= d_dev d < 256) by lia.
  assert (Rctr : 0 <= d_counter d < 256) by lia.
  unfold desk_cells in DK.
  unfold disj, RELRO_BASE, RELRO_LEN in HDJ.
  pose proof FR as FR0.
  destruct (body_cut e m1 k c rem tl FR) as (FA & BY & WB & FC). clear FR.
  rewrite HWR in FC.
  apply (rw_cells_split_at _ _ _ 11 80 tl [70;1;1;1;1;1;1;1;1;1;1]%nat) in FC; [| reflexivity | reflexivity].
  cbn [firstn skipn mk_CB_cells app] in FC.
  apply (rw_cells_split_at _ _ _ 5 24 (k_want k) [2;1;1;10;1;9]%nat) in FC; [| reflexivity | reflexivity].
  cbn [firstn skipn mk_CB_cells app] in FC.
  zstep. zstep. zstep.
  if_cases E1.
  - zify_cond E1.
    assert (Hb7 : 0x7f < k_b k) by (rewrite sx32_u in E1 by lia; destruct (Z.ltb_spec (k_b k) (2 ^ 31)); lia).
    zstep.
    eapply (owe_err_tail e fuel HE CHK) with (rc := E_RANGE);
      [ exact HF | exact HRC | exact HRCk | | | | exact HWL | exact HWK | exact HWD | exact HC | exact FR0 | exact HFR ].
    + unfold owe_k. rewrite HK. apply owe10_rng_b. lia.
    + unfold E_RANGE. lia.
    + first [ reflexivity | apply bv_eq; vm_compute; reflexivity ].
  - zify_cond E1.
    assert (Hb7 : k_b k <= 0x7f) by (rewrite sx32_u in E1 by lia; destruct (Z.ltb_spec (k_b k) (2 ^ 31)); lia).
    rewrite (sx32_small (k_b k)) by lia.
    zstep. zstep.
    sb_loop10 0%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
    sb_loop10 1%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
    sb_loop10 2%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
    sb_loop10 3%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
    sb_loop10 4%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
    sb_loop10 5%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
    sb_loop10 6%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_yes.
    sb_loop10 7%nat BY LB HE CHK HF HRC HRCk HWL HWK HWD HC FR0 HFR HK. br_not.
    zstep. cbv beta. rewrite (u8_unsigned (d_counter d)) by lia.
    do 13 zstep.
    try clear FR0.
    rev_loop 0 BY LB. br_yes.
    rev_loop 1 BY LB. br_yes.
    rev_loop 2 BY LB. br_yes.
    rev_loop 3 BY LB. br_yes.
    rev_loop 4 BY LB. br_yes.
    rev_loop 5 BY LB. br_yes.
    rev_loop 6 BY LB. br_yes.
    rev_loop 7 BY LB. br_not.
    zstep. cbv beta. rewrite (u8_unsigned (d_dev d)) by lia.
    do 9 zstep.
    assert (U114 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -114)) = bv_unsigned (e_sp e) + -114)
      by (apply unsigned_lit; lia).
    assert (U236 : bv_unsigned (Z_to_bv 64 (bv_unsigned (e_sp e) + -236)) = bv_unsigned (e_sp e) + -236)
      by (apply unsigned_lit; lia).
    assert (U10 : bv_unsigned (Z_to_bv 64 10) = 10) by reflexivity.
    destruct (rw_cells_isolate _ _ _ 17 10 FC) as (_ & S2 & _).
    apply rw_cells_bytes_at in S2.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in S2. fix_ofnat S2.
    replace (bv_unsigned (e_sp e) + -320 + 206) with (bv_unsigned (e_sp e) + -114) in S2 by lia.
    destruct (rw_cells_isolate _ _ _ 8 1 FC) as (Q1 & Q2 & Q3). clear FC.
    cbn [firstn skipn cells_size csize cells_bytes cbytes app Nat.add] in Q1, Q2, Q3.
    fix_ofnat Q2. fix_ofnat Q3.
    replace (bv_unsigned (e_sp e) + -320 + 84) with (bv_unsigned (e_sp e) + -236) in Q2, Q3 by lia.
    call MC.
    { rewrite U114. exact S2. }
    { reflexivity. }
    { rewrite U236. exact Q2. }
    { rewrite U114, U236. lia. }
    { assumption. }
    rewrite ?U114, ?U236 in *.
    match goal with T : rw_cells _ _ (bv_unsigned (e_sp e) + -236) _ |- _ =>
      rewrite U10 in T; change (Z.to_nat 10) with 10%nat in T; rename T into QT end.
    pose proof (rw_cells_join3n _ _ _ _ _ _ _ _ Q1 QT Q3 ltac:(cbn; lia) ltac:(cbn; lia)) as FC.
    clear Q1 QT Q3 POST S2. cbn [app] in FC.
    do 7 zstep. cbv beta. rewrite (u8_unsigned (d_counter d)) by lia.
    do 5 zstep.
    pose proof (rw_cells_merge_at _ _ _ 5 6 FC) as FM. clear FC.
    cbn [firstn skipn cells_size csize Nat.add app] in FM.
    pose proof (rw_cells_merge_at _ _ _ 11 11 FM) as FM2. clear FM.
    cbn [firstn skipn cells_size csize Nat.add app] in FM2.
    pose proof (body_glue e _ k c rem _ _ _ _ _ _ FA BY WB LB FM2) as FB. clear FM2.
    set (BS := [0xf0; 0x13; u8 (d_dev d); u8 0x30] ++ ([d_counter d; u8 (k_b k)] ++ rev (firstn 8 (zb (k_bytes k))))
                 ++ [0xf7]).
    assert (LBS : Z.of_nat (length BS) = 15)
      by (unfold BS; rewrite !length_app, length_rev, length_firstn; unfold zb; rewrite length_map, LB; reflexivity).
    lazymatch type of FB with rw_cells _ _ _ (body_cells _ (set_owe _ _ ?W _ _ _) _ _ ?T) =>
      eapply (owe_ok_tail e fuel CHK) with (bs := BS) (key := KEY 6 (d_counter d)) (dp := 1) (w := W) (tl := T) end;
      [ exact HF | exact HRC | exact HRCk | | | exact HC | | ].
    + unfold owe_k. rewrite HK. rewrite owe10_ok; [ unfold BS; reflexivity | lia | ].
      apply seven_bit_firstn_true.
      * unfold zb. rewrite length_map, LB. lia.
      * intros j Hj.
        assert (Ej : j = 0%nat \/ j = 1%nat \/ j = 2%nat \/ j = 3%nat \/ j = 4%nat \/ j = 5%nat \/ j = 6%nat \/ j = 7%nat)
          by lia.
        destruct Ej as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; apply sb_pos_nth; assumption.
    + unfold BS. clear - LB Hb7 Rdev Rctr.
      cbn [cells_bytes cbytes app]. rewrite le2_f013.
      repeat match goal with |- context [Z.to_nat ?z] =>
        lazymatch z with Zpos _ => idtac | Z0 => idtac end;
        let v := eval vm_compute in (Z.to_nat z) in progress change (Z.to_nat z) with v end.
      revert LB. generalize (k_bytes k). intros kb Lkb.
      do 8 (destruct kb as [|? kb]; [discriminate|]).
      cbn [firstn zb bz map app length rev nth]. rewrite ?firstn_O. cbn [firstn zb bz map app length rev nth].
      rewrite !b8_lit, !b8_u8, !b8_byte, b8_F7. reflexivity.
    + rewrite LBS.
      replace (KEY 6 (d_counter d)) with (Z.lor (d_counter d) 393216)
        by (rewrite (key_or 6 (d_counter d)) by lia; reflexivity).
      exact FB.
    + refine (conj _ (conj _ (conj _ (conj _ _)))); eassumption.
Qed.
