(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 604 of its 627 lines of code are new or changed and 122 lines of the source are left out. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Tac Bytes ZBridge.
From OSSVerify.Proofs.libreac.fuzz_scene.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import reac_scene_struct reac_ctrl_build_scene_step_c.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import RcModel RcParse.
From OSSVerify.Proofs.libreac.fuzz_scene.lib.Prog Require Import check_step_c bcmp_c memcpy_c reac_ctrl_parse_c reac_ctrl_checksum_verify_c.
Import ListNotations.
Open Scope Z_scope.

Ltac addr_eq_tac ::= first [ apply wa_of_var; lia
                           | symmetry; first [ apply wa_of_Z_to_bv; lia | apply wa_of_var; lia | unfold wa; f_equal; lia ] ].

Ltac slia ::= first [ exact I | lia | repeat split; try exact I; lia ].

Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  end.

Ltac norm_nat_lits :=
  repeat match goal with
  | H : context [Nat.of_num_uint ?u] |- _ =>
      let v := eval vm_compute in (Nat.of_num_uint u) in change (Nat.of_num_uint u) with v in H
  end.

Lemma scene_fields_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_fields b k) = 31%nat.
Proof.
  intros b k Hb Hk. norm_nat_lits. unfold scene_fields, scene_payload, scene_off.
  destruct (Z.eqb_spec k 0); [subst; cbn [length app]; rewrite length_firstn, Hb; reflexivity|].
  destruct (Z.eqb_spec k 342).
  - cbn [length app]. rewrite length_app, length_firstn, length_skipn, Hb. reflexivity.
  - cbn [length app]. rewrite length_firstn, length_skipn, Hb. lia.
Qed.

Lemma scene_block_length : forall b k, length b = 8904%nat -> 0 <= k <= 342 -> length (scene_block b k) = 34%nat.
Proof.
  intros b k Hb Hk. unfold scene_block. rewrite !length_app, scene_fields_length by assumption. reflexivity.
Qed.

Lemma cks_sum : forall S, 0 <= S -> (S + bv_unsigned (Z_to_bv 8 ((256 - S mod 256) mod 256))) mod 256 = 0.
Proof.
  intros S HS. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 2^8).
  Z.div_mod_to_equations. lia.
Qed.

Lemma byte_sum_nonneg : forall l, 0 <= byte_sum l.
Proof.
  induction l as [|x l IH]; cbn [byte_sum fold_right]; [lia|].
  pose proof (bv_unsigned_in_range 8 x). unfold byte_sum in IH. lia.
Qed.

Lemma ro_of_bytes : forall m A l, bytes_at rsegs m A l -> ro_cells rsegs m A (map C1 l).
Proof. intros m A l H. split; [apply cells_wf_map_C1 | rewrite cells_bytes_map_C1; exact H]. Qed.

Lemma memcmp_model_refl : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  intros l n. revert l. induction n as [|n IH]; intros [|x l] H; cbn in *; try lia; try reflexivity.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

Ltac split_first H A B NewH :=
  lazymatch type of H with
  | rw_cells ?segs ?mm A (?c :: ?rest) =>
      let H2 := fresh "Hs" in
      destruct (rw_cells_split2 mm A B [c] rest H ltac:(cbn [cells_size csize Nat.add]; lia)) as [NewH H2];
      clear H; rename H2 into H
  end.

Lemma payload0' : forall b, scene_payload b 0 = [Z_to_bv 8 0x22; Z_to_bv 8 0xc8] ++ firstn 24 b.
Proof. reflexivity. Qed.

Lemma firstn_firstn' : forall (l : list byte) n, firstn n (firstn n l) = firstn n l.
Proof. intros l n. rewrite firstn_firstn, Nat.min_id. reflexivity. Qed.

Lemma app_split_len : forall (l1 l2 l3 l4 : list byte), length l1 = length l3 -> l1 ++ l2 = l3 ++ l4 -> l1 = l3 /\ l2 = l4.
Proof.
  induction l1 as [|x l1 IH]; intros l2 [|y l3] l4 HL HE; cbn in *; try discriminate; [split; [reflexivity|exact HE]|].
  injection HE as -> HE. destruct (IH l2 l3 l4 ltac:(lia) HE) as [-> ->]. split; reflexivity.
Qed.

Lemma segK : forall K, K <> 0 -> K <> 342 -> scene_seg K = 0.
Proof. intros K H0 H1. unfold scene_seg. rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity. Qed.

Lemma lenK : forall K, K <> 0 -> K <> 342 -> scene_len K = 26.
Proof. intros K H0 H1. unfold scene_len. rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity. Qed.

Lemma payloadK : forall b K, K <> 0 -> K <> 342 ->
  scene_payload b K = firstn 26 (skipn (Z.to_nat (24 + 26 * (K - 1))) b).
Proof.
  intros b K H0 H1. unfold scene_payload, scene_off.
  rewrite (proj2 (Z.eqb_neq _ _) H0), (proj2 (Z.eqb_neq _ _) H1). reflexivity.
Qed.

Lemma off_eq : forall k, 1 <= k <= 341 ->
  Z.land 18446744073709551615 ((bv_swrap 32 (k + -1) mod 18446744073709551616 * 26 + 24) mod 18446744073709551616)
  = 24 + 26 * (k - 1).
Proof.
  intros k Hk.
  assert (SW : bv_swrap 32 (k + -1) = k + -1).
  { unfold bv_swrap, bv_wrap.
    replace (bv_half_modulus 32) with (2^31) by reflexivity.
    replace (bv_modulus 32) with (2^32) by reflexivity.
    rewrite Z.mod_small by lia. lia. }
  rewrite SW, Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  rewrite (Z.mod_small (k + -1)) by lia.
  rewrite (Z.mod_small ((k + -1) * 26 + 24)) by lia.
  rewrite Z.mod_small by lia. lia.
Qed.

Lemma lxor_small : forall x, 0 <= x < 2^63 -> Z.lxor x 9223372036854775808 = x + 9223372036854775808.
Proof.
  intros x Hx. rewrite <- Z.add_nocarry_lxor; [reflexivity|].
  apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, Z.bits_0.
  change 9223372036854775808 with (2^63). rewrite Z.pow2_bits_eqb by lia.
  destruct (Z.eqb_spec 63 n); [|apply andb_false_r].
  subst n. rewrite Z.bits_above_log2; [reflexivity|lia|].
  destruct (Z.eq_dec x 0); [subst; cbn; lia|]. apply Z.log2_lt_pow2; lia.
Qed.

Ltac zs := zstep; try (first [if_true | if_false]).

Ltac loop_turn := zstep; zstep; zstep; zstep; let K := fresh "K" in if_cases K; [clear K | zify_cond K; exfalso; lia].
Ltac loop_last := zstep; zstep; zstep; zstep; let K := fresh "K" in if_cases K; [zify_cond K; exfalso; lia | clear K].

Theorem check_step_holds :
  bcmp_contract -> memcpy_contract -> reac_ctrl_parse_contract -> reac_ctrl_checksum_verify_contract ->
  check_step_contract.
Proof.
  intros BCMP MEMC PARSE CKSV. unfold check_step_contract, CHECK_STEP, CHECK_STEP_K.
  unfold reac_ctrl_parse_contract, REAC_CTRL_PARSE_K in PARSE.
  unfold reac_ctrl_checksum_verify_contract in CKSV.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
         F fc m lo b HMI ST LO SP16 KR HBK HBB LB DBK DBB.
  norm_nat_lits.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp.
  pose proof (bv_unsigned_in_range 64 a0) as Ra0.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2.
  assert (Hbd : bv_unsigned a1 + 8904 <= 2^64)
    by (destruct (bytes_at_bound _ _ _ _ HBB) as [_ X]; rewrite LB in X; exact X).
  pose proof (scene_block_length b (bv_unsigned a2) LB ltac:(lia)) as LB34.
  assert (Hkd : bv_unsigned a0 + 34 <= 2^64)
    by (destruct (bytes_at_bound _ _ _ _ HBK) as [_ X]; rewrite LB34 in X; exact X).
  assert (LF : length (scene_fields b (bv_unsigned a2)) = 31%nat) by (apply scene_fields_length; [exact LB | lia]).
  set (B := scene_block b (bv_unsigned a2)) in *.
  assert (EB : scene_block b (bv_unsigned a2) = B) by reflexivity.
  clearbody B.
  destruct B as [|y0 B]; [discriminate LB34|].
  destruct B as [|y1 B]; [discriminate LB34|].
  destruct B as [|y2 B]; [discriminate LB34|].
  destruct B as [|y3 B]; [discriminate LB34|].
  destruct B as [|y4 B]; [discriminate LB34|].
  destruct B as [|y5 B]; [discriminate LB34|].
  destruct B as [|y6 B]; [discriminate LB34|].
  destruct B as [|y7 B]; [discriminate LB34|].
  destruct B as [|y8 B]; [discriminate LB34|].
  destruct B as [|y9 B]; [discriminate LB34|].
  destruct B as [|y10 B]; [discriminate LB34|].
  destruct B as [|y11 B]; [discriminate LB34|].
  destruct B as [|y12 B]; [discriminate LB34|].
  destruct B as [|y13 B]; [discriminate LB34|].
  destruct B as [|y14 B]; [discriminate LB34|].
  destruct B as [|y15 B]; [discriminate LB34|].
  destruct B as [|y16 B]; [discriminate LB34|].
  destruct B as [|y17 B]; [discriminate LB34|].
  destruct B as [|y18 B]; [discriminate LB34|].
  destruct B as [|y19 B]; [discriminate LB34|].
  destruct B as [|y20 B]; [discriminate LB34|].
  destruct B as [|y21 B]; [discriminate LB34|].
  destruct B as [|y22 B]; [discriminate LB34|].
  destruct B as [|y23 B]; [discriminate LB34|].
  destruct B as [|y24 B]; [discriminate LB34|].
  destruct B as [|y25 B]; [discriminate LB34|].
  destruct B as [|y26 B]; [discriminate LB34|].
  destruct B as [|y27 B]; [discriminate LB34|].
  destruct B as [|y28 B]; [discriminate LB34|].
  destruct B as [|y29 B]; [discriminate LB34|].
  destruct B as [|y30 B]; [discriminate LB34|].
  destruct B as [|y31 B]; [discriminate LB34|].
  destruct B as [|y32 B]; [discriminate LB34|].
  destruct B as [|y33 B]; [discriminate LB34|].
  destruct B; [|discriminate LB34]. clear LB34.
  assert (Y0 : y0 = Z_to_bv 8 0xcd) by exact (f_equal (fun l => nth 0 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y1 : y1 = Z_to_bv 8 0xea) by exact (f_equal (fun l => nth 1 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y2 : y2 = Z_to_bv 8 1) by exact (f_equal (fun l => nth 2 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y3 : y3 = Z_to_bv 8 (scene_seg (bv_unsigned a2))) by exact (f_equal (fun l => nth 3 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y4 : y4 = Z_to_bv 8 0) by exact (f_equal (fun l => nth 4 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y5 : y5 = Z_to_bv 8 (scene_len (bv_unsigned a2))) by exact (f_equal (fun l => nth 5 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (Y6 : y6 = Z_to_bv 8 0) by exact (f_equal (fun l => nth 6 l (Z_to_bv 8 0)) (eq_sym EB)).
  assert (SUM : (bv_unsigned y2 + bv_unsigned y3 + bv_unsigned y4 + bv_unsigned y5 + bv_unsigned y6 + bv_unsigned y7 + bv_unsigned y8 + bv_unsigned y9 + bv_unsigned y10 + bv_unsigned y11 + bv_unsigned y12 + bv_unsigned y13 + bv_unsigned y14 + bv_unsigned y15 + bv_unsigned y16 + bv_unsigned y17 + bv_unsigned y18 + bv_unsigned y19 + bv_unsigned y20 + bv_unsigned y21 + bv_unsigned y22 + bv_unsigned y23 + bv_unsigned y24 + bv_unsigned y25 + bv_unsigned y26 + bv_unsigned y27 + bv_unsigned y28 + bv_unsigned y29 + bv_unsigned y30 + bv_unsigned y31 + bv_unsigned y32 + bv_unsigned y33) mod 256 = 0).
  { assert (E : scene_fields b (bv_unsigned a2) ++
                [Z_to_bv 8 ((256 - byte_sum (scene_fields b (bv_unsigned a2)) mod 256) mod 256)]
                = [y2; y3; y4; y5; y6; y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32] ++ [y33]) by exact (f_equal (skipn 2) EB).
    apply app_inj_tail in E. destruct E as [EF EC].
    rewrite <- EC, EF.
    pose proof (cks_sum (byte_sum [y2; y3; y4; y5; y6; y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32]) (byte_sum_nonneg _)) as C.
    unfold byte_sum in C |- *. cbn [fold_right] in C |- *.
    match goal with |- ?X mod 256 = 0 => match type of C with ?Y mod 256 = 0 =>
      replace X with Y by lia; exact C end end. }
  pose proof (ro_of_bytes _ _ _ HBK) as HR. cbn [map] in HR.
  subst y0 y1 y2 y3 y4 y5 y6.
  pose proof (munch_refl [(bv_unsigned sp - 224, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  carve_frame 144%nat ST.
  apply (rw_cells_split_CB rsegs _ _ [] 144 junk [] [12; 36; 16; 34; 6; 40]%nat) in FR; [|reflexivity].
  cbn [app mk_CB_cells] in FR.
  split_first FR (bv_unsigned sp + -144) (bv_unsigned sp + -132) Q0.
  split_first FR (bv_unsigned sp + -132) (bv_unsigned sp + -96) PP.
  split_first FR (bv_unsigned sp + -96) (bv_unsigned sp + -80) II.
  split_first FR (bv_unsigned sp + -80) (bv_unsigned sp + -46) FT.
  split_first FR (bv_unsigned sp + -46) (bv_unsigned sp + -40) JJ.
  rename FR into SV.
  do 8 zstep.
  do 3 zstep; try if_false.
  do 3 zstep; try if_false.
  do 3 zstep; try if_false.
  do 2 zstep; try if_false.
  zstep. zstep.
  do 31 loop_turn.
  loop_last.
  zstep. zstep.
  pose proof (bv_unsigned_in_range 8 y7) as Ry7.
  pose proof (bv_unsigned_in_range 8 y8) as Ry8.
  pose proof (bv_unsigned_in_range 8 y9) as Ry9.
  pose proof (bv_unsigned_in_range 8 y10) as Ry10.
  pose proof (bv_unsigned_in_range 8 y11) as Ry11.
  pose proof (bv_unsigned_in_range 8 y12) as Ry12.
  pose proof (bv_unsigned_in_range 8 y13) as Ry13.
  pose proof (bv_unsigned_in_range 8 y14) as Ry14.
  pose proof (bv_unsigned_in_range 8 y15) as Ry15.
  pose proof (bv_unsigned_in_range 8 y16) as Ry16.
  pose proof (bv_unsigned_in_range 8 y17) as Ry17.
  pose proof (bv_unsigned_in_range 8 y18) as Ry18.
  pose proof (bv_unsigned_in_range 8 y19) as Ry19.
  pose proof (bv_unsigned_in_range 8 y20) as Ry20.
  pose proof (bv_unsigned_in_range 8 y21) as Ry21.
  pose proof (bv_unsigned_in_range 8 y22) as Ry22.
  pose proof (bv_unsigned_in_range 8 y23) as Ry23.
  pose proof (bv_unsigned_in_range 8 y24) as Ry24.
  pose proof (bv_unsigned_in_range 8 y25) as Ry25.
  pose proof (bv_unsigned_in_range 8 y26) as Ry26.
  pose proof (bv_unsigned_in_range 8 y27) as Ry27.
  pose proof (bv_unsigned_in_range 8 y28) as Ry28.
  pose proof (bv_unsigned_in_range 8 y29) as Ry29.
  pose proof (bv_unsigned_in_range 8 y30) as Ry30.
  pose proof (bv_unsigned_in_range 8 y31) as Ry31.
  pose proof (bv_unsigned_in_range 8 y32) as Ry32.
  pose proof (bv_unsigned_in_range 8 y33) as Ry33.
  pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (scene_seg (bv_unsigned a2)))) as Rseg.
  pose proof (bv_unsigned_in_range 8 (Z_to_bv 8 (scene_len (bv_unsigned a2)))) as Rlen.
  assert (U1 : bv_unsigned (Z_to_bv 8 1) = 1) by reflexivity.
  assert (U0 : bv_unsigned (Z_to_bv 8 0) = 0) by reflexivity.
  unfold bv_modulus in *.
  pose proof ST as (L0 & _ & _).
  assert (USP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -144)) = bv_unsigned sp + -144) by (rewrite unsigned_lit; lia).
  assert (UF80 : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80)) = bv_unsigned sp + -80) by (rewrite unsigned_lit; lia).
  assert (U34 : bv_unsigned (Z_to_bv 64 34) = 34) by reflexivity.
  if_cases KS.
  - exfalso. zify_cond KS. apply KS.
    match type of KS with Z.land ?X 255 <> 0 => match type of SUM with ?Y mod 256 = 0 =>
      replace X with Y by (rewrite ?U1, ?U0 in *; lia) end end.
    change 255 with (Z.ones 8). rewrite Z.land_ones by lia. exact SUM.
  - clear KS.
    zstep. if_cases K0; zify_cond K0.
    + destruct (Z.eq_dec (bv_unsigned a2) 342) as [K342|K342].
      * assert (EA : a2 = Z_to_bv 64 342) by (apply bv_eq; rewrite K342; reflexivity).
        subst a2. change (bv_unsigned (Z_to_bv 64 342)) with 342 in *.
        change (scene_seg 342) with 2 in *. change (scene_len 342) with 14 in *.
        do 29 zs.
        repeat match goal with |- context [Z.land ?x ?y] =>
          let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
        assert (UA : bv_unsigned (Z_to_bv 64 (bv_unsigned a1 + 8890)) = bv_unsigned a1 + 8890) by (rewrite unsigned_lit; lia).
        assert (UA7 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 7)) = bv_unsigned a0 + 7) by (rewrite unsigned_lit; lia).
        assert (E7 : (firstn 14 (skipn (Z.to_nat 8890) b) ++ scene_trailer) ++
                     [Z_to_bv 8 ((256 - byte_sum (scene_fields b 342) mod 256) mod 256)]
                     = [y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32] ++ [y33]) by exact (f_equal (skipn 7) EB).
        apply app_inj_tail in E7. destruct E7 as [E7 _].
        change [y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32] with ([y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20] ++ [y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32]) in E7.
        apply app_split_len in E7; [| rewrite length_firstn, length_skipn, LB; reflexivity].
        destruct E7 as [EPa EPt].
        pose proof (bytes_at_slice _ _ _ 7 14 HBK ltac:(cbn; lia)) as HL. cbn [firstn skipn] in HL.
        pose proof (bytes_at_slice _ _ _ (Z.to_nat 8890) 14 HBB ltac:(rewrite LB; apply Nat.leb_le; reflexivity)) as HRB.
        rewrite Z2Nat.id in HRB by lia.
        call BCMP.
        { rewrite UA7. exact HL. }
        { rewrite UA. exact HRB. }
        { change (Z.to_nat (bv_unsigned (Z_to_bv 64 14))) with 14%nat. rewrite <- EPa.
          apply memcmp_model_refl. rewrite length_firstn, length_skipn, LB. apply Nat.leb_le. reflexivity. }
        { assumption. }
        do 8 zs.
        assert (UA21 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 21)) = bv_unsigned a0 + 21) by (rewrite unsigned_lit; lia).
        pose proof (bytes_at_slice _ _ _ 21 12 HBK ltac:(cbn; lia)) as HL2. cbn [firstn skipn] in HL2.
        match goal with HMI' : mem_inv rsegs ?mm |- _ =>
          assert (HT : bytes_at rsegs mm 66454 scene_trailer)
            by (destruct (ro_cells_image rsegs mm 66454 scene_trailer HMI' ltac:(vm_compute; reflexivity)
                            ltac:(lia) ltac:(cbn; lia)) as [_ X];
                cbn [cells_bytes cbytes] in X; rewrite app_nil_r in X; exact X)
        end.
        call BCMP.
        { rewrite UA21. exact HL2. }
        { change (bv_unsigned (Z_to_bv 64 66454)) with 66454. exact HT. }
        { change (Z.to_nat (bv_unsigned (Z_to_bv 64 12))) with 12%nat. rewrite <- EPt.
          apply memcmp_model_refl. cbn. lia. }
        { assumption. }
        do 1 zs.
        do 7 zstep.
        do 2 zstep.
        do 3 zstep.
        zstep.
        call MEMC.
        { exact HBK. }
        { reflexivity. }
        { rewrite UF80, U34. change (Z.to_nat 34) with 34%nat. exact FT. }
        { rewrite UF80, U34. lia. }
        { assumption. }
        match goal with
        | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80))) _ |- _ =>
            rewrite UF80, U34 in P; change (Z.to_nat 34) with 34%nat in P; rename P into FT2
        end.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -80) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) FT2) as IF.
        pose proof (proj2 (proj1 IF)) as BF. cbn [cells_bytes cbytes app] in BF.
        pose proof (bytes_at_slice _ _ _ 2 32 (proj2 (proj1 FT2)) ltac:(cbn; lia)) as BC.
        cbn [cells_bytes cbytes app firstn skipn] in BC.
        replace (bv_unsigned sp + -80 + Z.of_nat 2) with (bv_unsigned sp + -96 + 18) in BC by lia.
        clear IF.
        do 3 zstep.
        zstep.
        lazymatch type of ST with stk _ ?mm _ _ =>
          destruct (stk_split rsegs mm lo (bv_unsigned sp + -144 - 80) (bv_unsigned sp + -144) ST ltac:(lia)) as [STa STb]
        end.
        clear ST.
        match type of BF with bytes_at _ _ _ ?L => eapply evt_cut; [ eapply PARSE with (fr := L) | ] end.
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        { lia. }
        { lia. }
        { lia. }
        { lia. }
        { Z.div_mod_to_equations. lia. }
        { lia. }
        { exact STb. }
        { assumption. }
        { reflexivity. }
        { intros _. lia. }
        { intros i Hi. pose proof (cp_rd_lt39 _ _ _ Hi) as Hi39. apply (proj2 (proj2 BF)).
          eapply Nat.lt_le_trans; [exact Hi39 | ]. apply Nat.leb_le. reflexivity. }
        { intros _. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact PP|]. split; [lia|]. intros _. lia. }
        intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
        unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc. rewrite (proj2 (Z.eqb_neq (bv_unsigned sp + -132) 0) ltac:(lia)) in MUc. cbn [app] in MUc.
        lazymatch type of MUc with munch _ ?mo ?mn =>
          transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
          try (match goal with H : mem_inv rsegs mo |- _ => clear H end); try clear mo
        end.
        destruct PO as [STp PO].
        specialize (PO ltac:(lia)).
        pose proof (stk_merge _ _ _ _ _ STa STp ltac:(lia)) as ST. clear STa STp.
        replace (ret_pc (Z_to_bv 64 87396)) with (Z_to_bv 64 87396) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        match type of PO with rw_cells rsegs ?mm (bv_unsigned sp + -132) [CB 36 (snd (ctrlparse 50 ?FB))] =>
          assert (KIND : fst (ctrlparse 50 FB) = 2) by reflexivity; rewrite KIND;
          apply (rw_cells_rebytes _ _ _ [CB 22 (firstn 22 (snd (ctrlparse 50 FB))); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 2);
                                        CB 2 [Z_to_bv 8 14; Z_to_bv 8 0]; C1 (Z_to_bv 8 0);
                                        CB 9 (skipn 27 (snd (ctrlparse 50 FB)))]) in PO;
          [ | cbn [cells_wf cell_wf]; repeat split; reflexivity | reflexivity ];
          rename PO into PP2
        end.
        do 13 zs.
        match type of BC with bytes_at _ _ _ ?L =>
          eapply evt_cut; [eapply CKSV with (p := bv_unsigned sp + -96) (bs := L);
                           [lia | lia | reflexivity | reflexivity | exact BC] | ]
        end.
        intros ms' PO. destruct PO as (a1' & a2' & a3' & EM). subst ms'.
        replace (ret_pc (Z_to_bv 64 87448)) with (Z_to_bv 64 87448) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        match goal with |- context [blocksum ?L] =>
          assert (BSUM : blocksum L = 0)
            by (unfold blocksum; cbn [psum nth];
                match goal with |- ?X mod 256 = 0 => match type of SUM with ?Y mod 256 = 0 =>
                  replace X with Y by lia; exact SUM end end);
          rewrite BSUM
        end.
        cbn [Z.eqb].
        zs.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -40) _ _ JJ ltac:(cbn [cells_size csize Nat.add]; lia) SV) as J1.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -46) _ _ FT2 ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J2.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -80) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) J2) as J3.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -96) _ _ PP2 ltac:(cbn [cells_size csize Nat.add]; lia) J3) as J4.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -132) _ _ Q0 ltac:(cbn [cells_size csize Nat.add]; lia) J4) as FR.
        clear J1 J2 J3 J4 JJ SV FT2 II PP2 Q0.
        cbn [app] in FR.
        do 5 zstep.
        zstep.
        release_frame FR ST (bv_unsigned sp).
        zstep.
        finish.

      * assert (SG : bv_signed a2 = bv_unsigned a2) by (rewrite zb_signed; destruct (Z.ltb_spec (bv_unsigned a2) (2^63)); lia).
        assert (SEGK : scene_seg (bv_unsigned a2) = 0) by (apply segK; assumption).
        assert (LENK : scene_len (bv_unsigned a2) = 26) by (apply lenK; assumption).
        rewrite SEGK, LENK in *.
        zstep.
        rewrite (lxor_small (bv_unsigned a2)) by lia.
        rewrite (proj2 (Z.ltb_lt (bv_unsigned a2 + 9223372036854775808) (342 + 9223372036854775808)) ltac:(lia)).
        cbn [Z.b2z].
        zs. zs.
        zs. zs.
        zs. zstep.
        if_cases K1; zify_cond K1; rewrite ?SG in K1; rewrite ?(lxor_small (bv_unsigned a2)) in K1 by lia;
          idtac.
        { exfalso. lia. }
        zs. zstep.
        if_cases K2; zify_cond K2; [exfalso; lia|].
        zs. do 5 zs.
        zs. zstep.
        rewrite (proj2 (Z.ltb_ge (bv_unsigned a2) 1) ltac:(lia)). cbn [Z.b2z].
        zstep.
        if_cases K3; zify_cond K3; rewrite ?SG in K3; rewrite ?(lxor_small (bv_unsigned a2)) in K3 by lia;
          try (exfalso; lia).
        do 4 zs.
        zs. zs. zstep.
        if_cases K4; zify_cond K4; try (exfalso; lia).
        do 6 zs.
        assert (UA7 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 7)) = bv_unsigned a0 + 7) by (rewrite unsigned_lit; lia).
        assert (E7 : scene_payload b (bv_unsigned a2) ++
                     [Z_to_bv 8 ((256 - byte_sum (scene_fields b (bv_unsigned a2)) mod 256) mod 256)]
                     = [y7; y8; y9; y10; y11; y12; y13; y14; y15; y16; y17; y18; y19; y20; y21; y22; y23; y24; y25; y26; y27; y28; y29; y30; y31; y32] ++ [y33]) by exact (f_equal (skipn 7) EB).
        apply app_inj_tail in E7. destruct E7 as [E7 _].
        rewrite payloadK in E7 by assumption.
        pose proof (bytes_at_slice _ _ _ 7 26 HBK ltac:(cbn; lia)) as HL. cbn [firstn skipn] in HL.
        pose proof (bytes_at_slice _ _ _ (Z.to_nat (24 + 26 * (bv_unsigned a2 - 1))) 26 HBB ltac:(rewrite LB; lia)) as HRB.
        call BCMP.
        { rewrite UA7. exact HL. }
        { rewrite (off_eq (bv_unsigned a2)) by lia. rewrite unsigned_lit by lia.
          rewrite <- (Z2Nat.id (24 + 26 * (bv_unsigned a2 - 1))) by lia. exact HRB. }
        { change (Z.to_nat (bv_unsigned (Z_to_bv 64 26))) with 26%nat. rewrite <- E7.
          apply memcmp_model_refl. rewrite length_firstn, length_skipn, LB. lia. }
        { assumption. }
        zs. zs. zstep.
        if_cases K5; zify_cond K5; try (exfalso; lia).
        do 7 zstep.
        do 2 zstep.
        do 3 zstep.
        zstep.
        call MEMC.
        { exact HBK. }
        { reflexivity. }
        { rewrite UF80, U34. change (Z.to_nat 34) with 34%nat. exact FT. }
        { rewrite UF80, U34. lia. }
        { assumption. }
        match goal with
        | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80))) _ |- _ =>
            rewrite UF80, U34 in P; change (Z.to_nat 34) with 34%nat in P; rename P into FT2
        end.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -80) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) FT2) as IF.
        pose proof (proj2 (proj1 IF)) as BF. cbn [cells_bytes cbytes app] in BF.
        pose proof (bytes_at_slice _ _ _ 2 32 (proj2 (proj1 FT2)) ltac:(cbn; lia)) as BC.
        cbn [cells_bytes cbytes app firstn skipn] in BC.
        replace (bv_unsigned sp + -80 + Z.of_nat 2) with (bv_unsigned sp + -96 + 18) in BC by lia.
        clear IF.
        do 3 zstep.
        zstep.
        lazymatch type of ST with stk _ ?mm _ _ =>
          destruct (stk_split rsegs mm lo (bv_unsigned sp + -144 - 80) (bv_unsigned sp + -144) ST ltac:(lia)) as [STa STb]
        end.
        clear ST.
        match type of BF with bytes_at _ _ _ ?L => eapply evt_cut; [ eapply PARSE with (fr := L) | ] end.
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        { lia. }
        { lia. }
        { lia. }
        { lia. }
        { Z.div_mod_to_equations. lia. }
        { lia. }
        { exact STb. }
        { assumption. }
        { reflexivity. }
        { intros _. lia. }
        { intros i Hi. pose proof (cp_rd_lt39 _ _ _ Hi) as Hi39. apply (proj2 (proj2 BF)).
          eapply Nat.lt_le_trans; [exact Hi39 | ]. apply Nat.leb_le. reflexivity. }
        { intros _. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact PP|]. split; [lia|]. intros _. lia. }
        intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
        unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc. rewrite (proj2 (Z.eqb_neq (bv_unsigned sp + -132) 0) ltac:(lia)) in MUc. cbn [app] in MUc.
        lazymatch type of MUc with munch _ ?mo ?mn =>
          transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
          try (match goal with H : mem_inv rsegs mo |- _ => clear H end); try clear mo
        end.
        destruct PO as [STp PO].
        specialize (PO ltac:(lia)).
        pose proof (stk_merge _ _ _ _ _ STa STp ltac:(lia)) as ST. clear STa STp.
        replace (ret_pc (Z_to_bv 64 87396)) with (Z_to_bv 64 87396) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        match type of PO with rw_cells rsegs ?mm (bv_unsigned sp + -132) [CB 36 (snd (ctrlparse 50 ?FB))] =>
          assert (KIND : fst (ctrlparse 50 FB) = 2) by reflexivity; rewrite KIND;
          apply (rw_cells_rebytes _ _ _ [CB 22 (firstn 22 (snd (ctrlparse 50 FB))); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 0);
                                        CB 2 [Z_to_bv 8 26; Z_to_bv 8 0]; C1 (Z_to_bv 8 0);
                                        CB 9 (skipn 27 (snd (ctrlparse 50 FB)))]) in PO;
          [ | cbn [cells_wf cell_wf]; repeat split; reflexivity | reflexivity ];
          rename PO into PP2
        end.
        do 13 zs.
        match type of BC with bytes_at _ _ _ ?L =>
          eapply evt_cut; [eapply CKSV with (p := bv_unsigned sp + -96) (bs := L);
                           [lia | lia | reflexivity | reflexivity | exact BC] | ]
        end.
        intros ms' PO. destruct PO as (a1' & a2' & a3' & EM). subst ms'.
        replace (ret_pc (Z_to_bv 64 87448)) with (Z_to_bv 64 87448) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
        match goal with |- context [blocksum ?L] =>
          assert (BSUM : blocksum L = 0)
            by (unfold blocksum; cbn [psum nth];
                match goal with |- ?X mod 256 = 0 => match type of SUM with ?Y mod 256 = 0 =>
                  replace X with Y by lia; exact SUM end end);
          rewrite BSUM
        end.
        cbn [Z.eqb].
        zs.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -40) _ _ JJ ltac:(cbn [cells_size csize Nat.add]; lia) SV) as J1.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -46) _ _ FT2 ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J2.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -80) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) J2) as J3.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -96) _ _ PP2 ltac:(cbn [cells_size csize Nat.add]; lia) J3) as J4.
        pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -132) _ _ Q0 ltac:(cbn [cells_size csize Nat.add]; lia) J4) as FR.
        clear J1 J2 J3 J4 JJ SV FT2 II PP2 Q0.
        cbn [app] in FR.
        do 5 zstep.
        zstep.
        release_frame FR ST (bv_unsigned sp).
        zstep.
        finish.
    + assert (EA : a2 = Z_to_bv 64 0) by (apply bv_eq; rewrite K0; reflexivity).
      subst a2. change (bv_unsigned (Z_to_bv 64 0)) with 0 in *.
      change (scene_seg 0) with 1 in *. change (scene_len 0) with 24 in *.
      do 29 zs.
      repeat match goal with |- context [Z.land ?x ?y] =>
        let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v end.
      assert (UA : bv_unsigned (Z_to_bv 64 (bv_unsigned a1 + 0)) = bv_unsigned a1) by (rewrite unsigned_lit; lia).
      assert (UA9 : bv_unsigned (Z_to_bv 64 (bv_unsigned a0 + 9)) = bv_unsigned a0 + 9) by (rewrite unsigned_lit; lia).
      assert (EP : firstn 24 (skipn 9 (scene_block b 0)) = firstn 24 b).
      { unfold scene_block, scene_fields. rewrite payload0'. cbn [skipn app]. rewrite ?skipn_O.
        rewrite firstn_app, length_firstn, LB. cbn [Nat.min Nat.sub firstn]. rewrite app_nil_r.
        apply firstn_firstn'. }
      rewrite EB in EP. cbn [firstn skipn] in EP.
      pose proof (bytes_at_slice _ _ _ 9 24 HBK ltac:(cbn; lia)) as HL. cbn [firstn skipn] in HL.
      pose proof (bytes_at_slice _ _ _ 0 24 HBB ltac:(rewrite LB; cbn; lia)) as HRB.
      change (skipn 0 b) with b in HRB. rewrite Z.add_0_r in HRB.
      call BCMP.
      { rewrite UA9. exact HL. }
      { rewrite UA. exact HRB. }
      { change (Z.to_nat (bv_unsigned (Z_to_bv 64 24))) with 24%nat. rewrite EP.
        apply memcmp_model_refl. rewrite length_firstn, LB. cbn. lia. }
      { assumption. }
      do 3 zs.
      do 7 zstep.
      do 2 zstep.
      do 3 zstep.
      zstep.
      call MEMC.
      { exact HBK. }
      { reflexivity. }
      { rewrite UF80, U34. change (Z.to_nat 34) with 34%nat. exact FT. }
      { rewrite UF80, U34. lia. }
      { assumption. }
      match goal with
      | P : rw_cells rsegs ?mm (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -80))) _ |- _ =>
          rewrite UF80, U34 in P; change (Z.to_nat 34) with 34%nat in P; rename P into FT2
      end.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -80) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) FT2) as IF.
      pose proof (proj2 (proj1 IF)) as BF. cbn [cells_bytes cbytes app] in BF.
      pose proof (bytes_at_slice _ _ _ 2 32 (proj2 (proj1 FT2)) ltac:(cbn; lia)) as BC.
      cbn [cells_bytes cbytes app firstn skipn] in BC.
      replace (bv_unsigned sp + -80 + Z.of_nat 2) with (bv_unsigned sp + -96 + 18) in BC by lia.
      clear IF.
      do 3 zstep.
      zstep.
      lazymatch type of ST with stk _ ?mm _ _ =>
        destruct (stk_split rsegs mm lo (bv_unsigned sp + -144 - 80) (bv_unsigned sp + -144) ST ltac:(lia)) as [STa STb]
      end.
      clear ST.
      match type of BF with bytes_at _ _ _ ?L => eapply evt_cut; [ eapply PARSE with (fr := L) | ] end.
      { reflexivity. }
      { reflexivity. }
      { reflexivity. }
      { reflexivity. }
      { lia. }
      { lia. }
      { lia. }
      { lia. }
      { Z.div_mod_to_equations. lia. }
      { lia. }
      { exact STb. }
      { assumption. }
      { reflexivity. }
      { intros _. lia. }
      { intros i Hi. pose proof (cp_rd_lt39 _ _ _ Hi) as Hi39. apply (proj2 (proj2 BF)).
        eapply Nat.lt_le_trans; [exact Hi39 | ]. apply Nat.leb_le. reflexivity. }
      { intros _. split; [Z.div_mod_to_equations; lia|]. split; [lia|]. split; [exact PP|]. split; [lia|]. intros _. lia. }
      intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
      unfold reac_ctrl_parse_fp, REAC_CTRL_PARSE_K in MUc. rewrite (proj2 (Z.eqb_neq (bv_unsigned sp + -132) 0) ltac:(lia)) in MUc. cbn [app] in MUc.
      lazymatch type of MUc with munch _ ?mo ?mn =>
        transport_after_call rsegs mo mn MUc WMc; clear MUc WMc;
        try (match goal with H : mem_inv rsegs mo |- _ => clear H end); try clear mo
      end.
      destruct PO as [STp PO].
      specialize (PO ltac:(lia)).
      pose proof (stk_merge _ _ _ _ _ STa STp ltac:(lia)) as ST. clear STa STp.
      replace (ret_pc (Z_to_bv 64 87396)) with (Z_to_bv 64 87396) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      match type of PO with rw_cells rsegs ?mm (bv_unsigned sp + -132) [CB 36 (snd (ctrlparse 50 ?FB))] =>
        assert (KIND : fst (ctrlparse 50 FB) = 2) by reflexivity; rewrite KIND;
        apply (rw_cells_rebytes _ _ _ [CB 22 (firstn 22 (snd (ctrlparse 50 FB))); C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1);
                                      CB 2 [Z_to_bv 8 24; Z_to_bv 8 0]; C1 (Z_to_bv 8 0);
                                      CB 9 (skipn 27 (snd (ctrlparse 50 FB)))]) in PO;
        [ | cbn [cells_wf cell_wf]; repeat split; reflexivity | reflexivity ];
        rename PO into PP2
      end.
      do 13 zs.
      match type of BC with bytes_at _ _ _ ?L =>
        eapply evt_cut; [eapply CKSV with (p := bv_unsigned sp + -96) (bs := L);
                         [lia | lia | reflexivity | reflexivity | exact BC] | ]
      end.
      intros ms' PO. destruct PO as (a1' & a2' & a3' & EM). subst ms'.
      replace (ret_pc (Z_to_bv 64 87448)) with (Z_to_bv 64 87448) by (symmetry; apply ret_pc_even; [lia | reflexivity]).
      match goal with |- context [blocksum ?L] =>
        assert (BSUM : blocksum L = 0)
          by (unfold blocksum; cbn [psum nth];
              match goal with |- ?X mod 256 = 0 => match type of SUM with ?Y mod 256 = 0 =>
                replace X with Y by lia; exact SUM end end);
        rewrite BSUM
      end.
      cbn [Z.eqb].
      zs.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -40) _ _ JJ ltac:(cbn [cells_size csize Nat.add]; lia) SV) as J1.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -46) _ _ FT2 ltac:(cbn [cells_size csize Nat.add]; lia) J1) as J2.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -80) _ _ II ltac:(cbn [cells_size csize Nat.add]; lia) J2) as J3.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -96) _ _ PP2 ltac:(cbn [cells_size csize Nat.add]; lia) J3) as J4.
      pose proof (rw_cells_join2 _ _ (bv_unsigned sp + -132) _ _ Q0 ltac:(cbn [cells_size csize Nat.add]; lia) J4) as FR.
      clear J1 J2 J3 J4 JJ SV FT2 II PP2 Q0.
      cbn [app] in FR.
      do 5 zstep.
      zstep.
      release_frame FR ST (bv_unsigned sp).
      zstep.
      finish.
Qed.
