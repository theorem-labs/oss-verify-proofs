(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Step.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Tac OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib.Step.ZBridge.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require ImgFacts Bigint_defs Wbig_tac Wdc_tac U_pow5_stmt U_shl_stmt U_memset_stmt U_normalize_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_memset_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_negative_digit_comp_d_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.ImgFacts OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wdc_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_normalize_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_memset_stmt.U_compare_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_negative_digit_comp_d_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Local Ltac post_call segs m ::=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let W' := eval hnf in W in change (munch W' m m') in MUc;
      transport_after_call segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).

(* [comment removed for export] *)
Lemma u64arr_cons : forall m A v ws,
  rw_cells USEGS m A [C8 v] -> u64arr USEGS m (A + 8) ws -> u64arr USEGS m A (v :: ws).
Proof.
  intros m A v ws [[_ Hb] Hw] [Hb2 Hw2]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize Nat.add] in Hw.
  split.
  - cbn [u64s map concat]. change (le8 v ++ u64s ws) with (le8 v ++ u64s ws).
    apply (proj2 (bytes_at_app USEGS m A (le8 v) (u64s ws))). split; [exact Hb|].
    rewrite length_le8. exact Hb2.
  - cbn [length]. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat (length ws)))%Z with (8 + 8 * Z.of_nat (length ws))%Z by lia.
    apply (proj2 (wr_at_app USEGS m A 8 (8 * Z.of_nat (length ws)) ltac:(lia) ltac:(lia))). split; [exact Hw| exact Hw2].
Qed.

Lemma pow5_1300 : (5 ^ 1300 < 2 ^ 3019)%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Lemma cap_neg : forall b k, (0 <= b < 2^64)%Z -> (0 <= k <= 1300)%Z -> (b * 5 ^ k < BIG_CAP)%Z.
Proof.
  intros b k Hb Hk. unfold BIG_CAP.
  assert (5 ^ k <= 5 ^ 1300)%Z by (apply Z.pow_le_mono_r; lia).
  assert (0 < 5 ^ k)%Z by (apply Z.pow_pos_nonneg; lia).
  pose proof pow5_1300.
  assert (2 ^ 64 * 2 ^ 3019 <= 2 ^ 3968)%Z by (rewrite <- Z.pow_add_r by lia; apply Z.pow_le_mono_r; lia).
  nia.
Qed.

(* [comment removed for export] *)
Lemma bval_1 : forall (w : word) ws, bval (w :: ws) 1 = bv_unsigned w.
Proof. intros. cbn [bval]. unfold limbZ. cbn [nth]. change (2 ^ (64 * Z.of_nat 0))%Z with 1%Z. lia. Qed.

(* [comment removed for export] *)
Ltac pose_sp_lits sp :=
  repeat match goal with |- context [Some (Z_to_bv 64 (bv_unsigned sp + ?k)%Z)] =>
    lazymatch goal with
    | _ : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + k)%Z) = _ |- _ => fail
    | _ => pose proof (unsigned_lit (bv_unsigned sp + k)%Z ltac:(lia))
    end end.
Ltac rewrite_sp_lits sp :=
  repeat match goal with U : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + ?k)%Z) = _ |- _ => rewrite !U end.
Ltac rewrite_sp_lits_all sp :=
  repeat match goal with U : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + ?k)%Z) = _ |- _ => rewrite !U in *; clear U end.

Section Main.
  Hypothesis memset_spec : memset_stmt.
  Hypothesis normalize_spec : normalize_stmt.
  Hypothesis pow5_spec : pow5_stmt.
  Hypothesis shl_spec : shl_stmt.
  Hypothesis compare_spec : compare_stmt.

  #[using="memset_spec normalize_spec pow5_spec shl_spec compare_spec"] Lemma negative_digit_comp_d_spec : negative_digit_comp_d_stmt.
  Proof. LiaFast.lf_pins (fun (memset_spec normalize_spec pow5_spec shl_spec compare_spec : LiaFast.U) => LiaFast.u0).
    unfold negative_digit_comp_d_stmt. intros until e. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NZ NORM Hp2 Rp2 He Re SEP.
    pose proof (munch_refl (negative_digit_comp_d_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [negative_digit_comp_d_W] in MU.
    pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
    subst a3.
    pose proof (u64arr_outside_rodata_U _ _ _ PR LIMBS ltac:(rewrite L62; lia)) as ARO1. rewrite L62 in ARO1.
    pose proof (rw_cells_outside_rodata_U _ _ _ PR LENC ltac:(cbn; lia)) as ARO2. cbn [cells_size csize Nat.add] in ARO2.
    carve_frame 576%nat ST.
    do 10 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) rewrite Hp2, uw_mod32, Z.add_0_r, (swrap32_id p2) by lia.
    step. (* [comment removed for export] *) rewrite uw_sub, (swrap32_id (0 - p2)) by lia. rewrite (Z.sub_0_l p2).
    step. (* [comment removed for export] *) rewrite ?word_sub_lit2, ?word_sub_lit. rewrite (Z.sub_0_l p2).
    step. (* [comment removed for export] *) if_not_taken.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    set (POSTC := negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m).
    set (SPW := Z_to_bv 64 (bv_unsigned sp + -576)).
    (* [comment removed for export] *)
    assert (J6c : forall (q7 : Z) (v10 v11 v12 v13 : word), (-1076 <= q7 <= 971)%Z ->
      evt USEGS POSTC
        (MS (mkR ra SPW gp tp t0 t1 t2 a2 a1 v10 v11 v12 v13 a4 a5 a6 a7
                 a0 (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (- p2)) s6 (Z_to_bv 64 q7) s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26afc) fc None m0 (seg_rom USEGS))).
    { intros q7 v10 v11 v12 v13 Hq7. subst SPW.
      gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *) gen_reg (22:reg).
      (* [comment removed for export] *)
      eapply (rw_cells_split_CB USEGS _ _ [] 504 _ _ [8; 496]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
      chunk_split FR 1%nat FR0 FRr. chunk_split FRr 1%nat FRo FRsv.
      lazymatch type of FRo with rw_cells _ _ _ [CB 496 ?l] =>
        assert (LJ : length l = 496%nat) by exact (proj1 (proj1 (proj1 FRo))) end.
      pose proof (u8arr_of_rw_cells _ _ _ _ _ FRo) as OLD. clear FRo.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose_sp_lits sp. pose proof (unsigned_lit 496 ltac:(lia)) as U496.
      step. (* [comment removed for export] *)
      call memset_spec.
      { reflexivity. }
      { rewrite_sp_lits sp. exact OLD. }
      { rewrite U496, LJ. reflexivity. }
      { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
      rewrite_sp_lits_all sp. rewrite -> ?U496 in *. clear U496 LJ.
      change (Z.to_nat 496) with 496%nat in *.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
        lazymatch goal with M : bytes_at _ m' _ (repeat _ _), Wt : wr_at _ m' _ _ |- _ =>
          rename M into ZB; rename Wt into ZW; rename m' into m1 end end.
      replace (repeat (Z_to_bv 8 0) 496) with (repeat (Z_to_bv 8 0) (8 * 61) ++ (repeat (Z_to_bv 8 0) 2 ++ repeat (Z_to_bv 8 0) 6))
        in ZB by reflexivity.
      apply bytes_at_app in ZB. destruct ZB as [ZBL ZB26]. rewrite repeat_length in ZB26.
      apply bytes_at_app in ZB26. destruct ZB26 as [ZB2 ZB6]. rewrite repeat_length in ZB6.
      rewrite repeat_length in ZW. change (Z.of_nat 496) with (488 + (2 + 6))%Z in ZW.
      apply wr_at_app in ZW; [|lia|lia]. destruct ZW as [ZWL ZW26].
      apply wr_at_app in ZW26; [|lia|lia]. destruct ZW26 as [ZW2 ZW6].
      change (Z.of_nat (8 * 61)) with 488%Z in ZB2, ZB6. change (Z.of_nat 2) with 2%Z in ZB6.
      replace (bv_unsigned sp + -568 + 488)%Z with (bv_unsigned sp + -80)%Z in ZB2, ZW2 by lia.
      replace (bv_unsigned sp + -568 + 488 + 2)%Z with (bv_unsigned sp + -78)%Z in ZB6, ZW6 by lia.
      pose proof (rw_cells_of_u8arr USEGS _ _ _ (conj ZB2 ZW2)) as LENT. clear ZB2 ZW2. rewrite repeat_length in LENT.
      pose proof (rw_cells_of_u8arr USEGS _ _ _ (conj ZB6 ZW6)) as PADT. clear ZB6 ZW6. rewrite repeat_length in PADT.
      pose proof (rw_cells_of_u8arr USEGS _ _ _ (conj ZBL ZWL)) as LIML. clear ZBL ZWL. rewrite repeat_length in LIML.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename m' into m2 end.
      destruct (u64arr_of_rw_cells USEGS _ _ 61 _ LIML) as (wsz & Lz & LIMBT). clear LIML.
      replace (bv_unsigned sp + -568)%Z with (bv_unsigned sp + -576 + 8)%Z in LIMBT by lia.
      pose proof (u64arr_cons _ _ _ _ FR0 LIMBT) as LIMT. clear FR0 LIMBT.
      replace (bv_unsigned sp + -80)%Z with (bv_unsigned sp + -576 + 496)%Z in LENT by lia.
      assert (LT62 : length (rv2 :: wsz) = 62%nat) by (cbn [length]; rewrite Lz; reflexivity).
      step. (* [comment removed for export] *)
      pose_sp_lits sp.
      step. (* [comment removed for export] *)
      call normalize_spec.
      { rewrite_sp_lits sp. exact LIMT. }
      { exact LT62. }
      { rewrite_sp_lits sp. exact LENT. }
      { lia. }
      rewrite_sp_lits_all sp.
      rename MI into LIMT2. rename POST into LENT2.
      change (Z.to_nat 1) with 1%nat in LENT2.
      set (nl := norm_len (rv2 :: wsz) 1) in LENT2.
      assert (Hnl : (nl <= 1)%nat) by (subst nl; apply norm_len_le).
      assert (NORMT : bnorm (rv2 :: wsz) (Z.to_nat (Z.of_nat nl))) by (rewrite Nat2Z.id; subst nl; apply norm_len_bnorm).
      assert (BVT : bval (rv2 :: wsz) (Z.to_nat (Z.of_nat nl)) = bv_unsigned rv2).
      { rewrite Nat2Z.id. subst nl. rewrite norm_len_bval. apply bval_1. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename m' into m3 end.
      step. (* [comment removed for export] *) rewrite uw_sub2, (swrap32_id (q7 - e)) by lia. rewrite <- (Z.add_opp_r q7 e).
      step. (* [comment removed for export] *) rewrite word_sub_lit2. rewrite <- (Z.add_opp_r q7 e).
      step. (* [comment removed for export] *) if_not_taken.
      step. (* [comment removed for export] *) rewrite uw_sub, (swrap32_id (0 - e)) by lia. rewrite (Z.sub_0_l e).
      step. (* [comment removed for export] *) rewrite ?word_sub_lit2, ?word_sub_lit. rewrite (Z.sub_0_l e).
      step. (* [comment removed for export] *) if_not_taken.
      step. (* [comment removed for export] *) trap_dead.
      step. (* [comment removed for export] *)
      pose_sp_lits sp.
      pose proof (bv_unsigned_in_range 64 rv2) as Rrv2. unfold bv_modulus in Rrv2.
      step. (* [comment removed for export] *)
      call pow5_spec.
      { rewrite_sp_lits sp. replace (bv_unsigned sp + -576 - 1296)%Z with (bv_unsigned sp - 1872)%Z by lia. exact ST. }
      { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
      { rewrite_sp_lits sp. lia. }
      { eassumption. }
      { rewrite_sp_lits sp. exact LIMT2. }
      { exact LT62. }
      { rewrite_sp_lits sp. exact LENT2. }
      { lia. }
      { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
      { rewrite_sp_lits sp. lia. }
      { exact NORMT. }
      { rewrite unsigned_lit by lia. lia. }
      { rewrite unsigned_lit by lia. rewrite BVT. apply cap_neg; lia. }
      { rewrite_sp_lits sp. lia. }
      rewrite_sp_lits_all sp.
      clear NORMT BVT LT62 Hnl. rename MI into STp. rename PC into LIMT. rename PC0 into LT62. rename PC1 into LENT.
      rename PC2 into HlenT. clear PC3 PC4. try clear PR. rename POST into PR.
      lazymatch type of LIMT with u64arr _ ?mq _ ?wq => rename mq into m4; rename wq into wst end.
      lazymatch type of HlenT with (0 <= ?l <= 62)%Z => rename l into lent end.
      rename STp into ST. replace (bv_unsigned sp + -576 - 1296)%Z with (bv_unsigned sp - 1872)%Z in ST by lia.
      try clear LIMT2. try clear LENT2. subst nl || idtac.
      (* [comment removed for export] *)
      assert (JE0 : forall (m5 : word -> option byte) (wsr wst' : list word) (lenr lent' : Z)
                           (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v22 v23 v28 v29 v30 v31 : word),
        u64arr USEGS m5 (bv_unsigned a0) wsr -> length wsr = 62%nat ->
        rw_cells USEGS m5 (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 lenr)] -> (0 <= lenr <= 62)%Z ->
        u64arr USEGS m5 (bv_unsigned sp + -576) wst' -> length wst' = 62%nat ->
        rw_cells USEGS m5 (bv_unsigned sp + -576 + 496) [C2 (Z_to_bv 64 lent')] -> (0 <= lent' <= 62)%Z ->
        rw_cells USEGS m5 (bv_unsigned sp + -78) [CB 6 (repeat (Z_to_bv 8 0) 6)] ->
        rw_cells USEGS m5 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk USEGS m5 (bv_unsigned sp - 1872) (bv_unsigned sp + -576) ->
        munch [((bv_unsigned sp - 1872)%Z, bv_unsigned sp); (bv_unsigned a0, (bv_unsigned a0 + 498)%Z)] m m5 ->
        wmono USEGS m m5 ->
        evt USEGS POSTC
          (MS (mkR v1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp v5 v6 v7 a2 a1 v10 v11 v12 v13 v14 v15 v16 v17
                   a0 (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (- p2)) v22 v23 s8 s9 s10 s11 v28 v29 v30 v31)
              F (Z_to_bv 64 0x26b70) fc None m5 (seg_rom USEGS))).
      { intros m5 wsr wst' lenr lent' y1 y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31
               LIR LR LER HLR LIT LT LET HLT PAD SAV ST5 MU5 WM5.
        clear LIMT LT62 LENT HlenT PADT FRsv PR MU WM Lz wsz ST LIMBS LENC.
        step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        pose_sp_lits sp.
        step. (* [comment removed for export] *)
        call compare_spec.
        { exact LIR. } { exact LR. } { exact LER. } { exact HLR. }
        { rewrite_sp_lits sp. exact LIT. } { exact LT. } { rewrite_sp_lits sp. exact LET. } { exact HLT. }
        rewrite_sp_lits_all sp.
        (* [comment removed for export] *)
        assert (JA8 : forall w1 w5 w6 w7 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w28 w29 w30 w31 : word,
          evt USEGS POSTC
            (MS (mkR w1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp w5 w6 w7 a2 w9 w10 w11 w12 w13 w14 w15 w16 w17
                     w18 w19 w20 w21 w22 w23 s8 s9 s10 s11 w28 w29 w30 w31)
                F (Z_to_bv 64 0x26c38) fc None m5 (seg_rom USEGS))).
        { intros.
          do 5 gstep. (* [comment removed for export] *)
          do 9 step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          pose proof (rw_cells_of_u64arr USEGS _ _ _ LIT) as OBJ. rewrite LT in OBJ. clear LIT.
          replace (bv_unsigned sp + -576 + 496)%Z with (bv_unsigned sp + -80)%Z in LET by lia.
          chunk_join OBJ LET FRa. chunk_join FRa PAD FRb. chunk_join FRb SAV FR.
          release_frame FR ST5 (bv_unsigned sp).
          subst POSTC. unfold negative_digit_comp_d_post. finish.
          all: try eassumption. all: try lia. }
        assert (J78 : forall w1 w5 w6 w7 w9 w10 w11 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w28 w29 w30 w31 : word,
          evt USEGS POSTC
            (MS (mkR w1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp w5 w6 w7 a2 w9 w10 w11 w12 w13 w14 w15 w16 w17
                     w18 w19 w20 w21 w22 w23 s8 s9 s10 s11 w28 w29 w30 w31)
                F (Z_to_bv 64 0x26c08) fc None m5 (seg_rom USEGS))).
        { intros. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hq.
          - clear Hq. gstep. gstep. step. apply JA8.
          - clear Hq. step. (* [comment removed for export] *) gstep. gstep. step. apply JA8. }
        assert (J50 : forall (q : Z) (w1 w5 w6 w7 w9 w10 w12 w13 w14 w15 w16 w17 w18 w19 w20 w21 w22 w23 w28 w29 w30 w31 : word),
          (-2^20 <= q <= 2^20)%Z ->
          evt USEGS POSTC
            (MS (mkR w1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp w5 w6 w7 a2 w9 w10 (Z_to_bv 64 q) w12 w13 w14 w15 w16 w17
                     w18 w19 w20 w21 w22 w23 s8 s9 s10 s11 w28 w29 w30 w31)
                F (Z_to_bv 64 0x26be0) fc None m5 (seg_rom USEGS))).
        { intros q. intros. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hq.
          - clear Hq. step. (* [comment removed for export] *) rewrite uw_add, (swrap32_id (q + 1)) by lia.
            step. (* [comment removed for export] *) trap_dead.
            step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J78.
          - clear Hq. gstep. gstep. step. apply J78. }
        assert (J1c : forall (u : Z) (w1 w5 w6 w7 w10 w12 w13 w14 w15 w16 w17 w22 w23 w28 w29 w30 w31 : word),
          (11 <= u <= 63)%Z -> (u <= - p2)%Z ->
          evt USEGS POSTC
            (MS (mkR w1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp w5 w6 w7 a2 a1 w10 (Z_to_bv 64 u) w12 w13 w14 w15 w16 w17
                     a0 (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (- p2)) w22 w23 s8 s9 s10 s11 w28 w29 w30 w31)
                F (Z_to_bv 64 0x26bac) fc None m5 (seg_rom USEGS))).
        { intros u. intros.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *) rewrite ?word_add_lit2.
          step. (* [comment removed for export] *) rewrite ?uw_add2, (swrap32_id (p2 + (u + 1))) by lia.
          step. (* [comment removed for export] *) if_not_taken.
          gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hq.
          - clear Hq. gstep. gstep. (* [comment removed for export] *) gstep. gstep. gstep. apply JA8.
          - clear Hq. step. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. gstep. gstep. apply JA8. }
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hd2.
        - cond_cleanup Hd2. rewrite ?signed_lit in Hd2 by lia.
          step. (* [comment removed for export] *) step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hq.
          + cond_cleanup Hq. apply J1c; lia.
          + cond_cleanup Hq. step. (* [comment removed for export] *) apply J1c; lia.
        - cond_cleanup Hd2. rewrite ?signed_lit in Hd2 by lia.
          step. (* [comment removed for export] *) rewrite Hp2, uw_mod32, (swrap32_id (p2 + 11)) by lia.
          step. (* [comment removed for export] *) trap_dead.
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hq.
          + clear Hq. gstep. gstep. (* [comment removed for export] *) apply J50. lia.
          + clear Hq. step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J50. lia. }
      (* [comment removed for export] *)
      assert (JCC : forall (v : Z) (onlocal : bool) (m5 : word -> option byte) (wsr wst' : list word) (lenr lent' : Z)
                           (y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31 : word),
        (0 < v < 2^31)%Z ->
        u64arr USEGS m5 (bv_unsigned a0) wsr -> length wsr = 62%nat ->
        rw_cells USEGS m5 (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 lenr)] -> (0 <= lenr <= 62)%Z ->
        u64arr USEGS m5 (bv_unsigned sp + -576) wst' -> length wst' = 62%nat ->
        rw_cells USEGS m5 (bv_unsigned sp + -576 + 496) [C2 (Z_to_bv 64 lent')] -> (0 <= lent' <= 62)%Z ->
        rw_cells USEGS m5 (bv_unsigned sp + -78) [CB 6 (repeat (Z_to_bv 8 0) 6)] ->
        rw_cells USEGS m5 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk USEGS m5 (bv_unsigned sp - 1872) (bv_unsigned sp + -576) ->
        munch [((bv_unsigned sp - 1872)%Z, bv_unsigned sp); (bv_unsigned a0, (bv_unsigned a0 + 498)%Z)] m m5 ->
        wmono USEGS m m5 ->
        evt USEGS POSTC
          (MS (mkR y1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp y5 y6 y7 a2 a1
                   (if onlocal then Z_to_bv 64 (bv_unsigned sp + -576) else a0) y11 y12 y13 y14 y15 y16 y17
                   a0 (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (- p2)) (Z_to_bv 64 v) y23 s8 s9 s10 s11 y28 y29 y30 y31)
              F (Z_to_bv 64 0x26b5c) fc None m5 (seg_rom USEGS))).
      { intros v onlocal m5 wsr wst' lenr lent' y1 y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y23 y28 y29 y30 y31
               Hv LIR LR LER HLR LIT LT LET HLT PAD SAV ST5 MU5 WM5.
        clear LIMT LT62 LENT HlenT PADT FRsv PR MU WM Lz wsz ST LIMBS LENC.
        step. (* [comment removed for export] *) rewrite (unsigned_lit v) by lia. rewrite (Z.shiftl_mul_pow2 v 32) by lia.
        step. (* [comment removed for export] *) rewrite (unsigned_lit (v * 2 ^ 32)) by lia. rewrite (Z.shiftr_div_pow2 _ 32) by lia.
        rewrite (Z.div_mul v (2 ^ 32)) by lia.
        pose_sp_lits sp.
        destruct (stk_split _ _ _ (bv_unsigned sp + -576 - 144)%Z _ ST5 ltac:(lia)) as [STlo SThi]. clear ST5.
        destruct onlocal.
        - step. (* [comment removed for export] *)
          call shl_spec.
          { rewrite_sp_lits sp. exact SThi. }
          { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
          { rewrite_sp_lits sp. exact LIT. } { exact LT. } { rewrite_sp_lits sp. exact LET. } { exact HLT. }
          { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
          { rewrite_sp_lits sp. lia. }
          { rewrite_sp_lits sp. lia. }
          rewrite_sp_lits_all sp.
          step. (* [comment removed for export] *)
          pose proof (stk_merge _ _ _ _ _ STlo MI ltac:(lia)) as ST6.
          eapply JE0; [exact LIR | exact LR | exact LER | exact HLR | exact PC | exact PC0 | exact PC1 | exact PC2
                      | exact PAD | exact SAV | exact ST6 | exact MU5 | exact WM5].
        - step. (* [comment removed for export] *)
          call shl_spec.
          { rewrite_sp_lits sp. exact SThi. }
          { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
          { exact LIR. } { exact LR. } { exact LER. } { exact HLR. } { exact A8. } { exact NZ. }
          { rewrite_sp_lits sp. lia. }
          rewrite_sp_lits_all sp.
          step. (* [comment removed for export] *)
          pose proof (stk_merge _ _ _ _ _ STlo MI ltac:(lia)) as ST6.
          eapply JE0; [exact PC | exact PC0 | exact PC1 | exact PC2 | exact LIT | exact LT | exact LET | exact HLT
                      | exact PAD | exact SAV | exact ST6 | exact MU5 | exact WM5]. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hle.
      - cond_cleanup Hle. assert (Hle' : (q7 + - e <= 0)%Z) by mlia. try clear Hle.
        step. (* [comment removed for export] *)
        if_cases Hlt.
        + cond_cleanup Hlt. assert (Hlt' : (q7 + - e < 0)%Z) by mlia. try clear Hlt.
          step. (* [comment removed for export] *) rewrite ?word_sub_lit2, ?word_sub_lit.
          step. (* [comment removed for export] *) rewrite uw_sub, (swrap32_id (0 - (q7 + - e))) by lia.
          step. (* [comment removed for export] *) if_not_taken.
          step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
          replace (0 - (q7 + - e))%Z with (e + - q7)%Z by lia.
          eapply (JCC (e + - q7)%Z false); [mlia | exact LIMBS | exact L62 | exact LENC | exact Hlen | exact LIMT | exact LT62 | exact LENT | exact HlenT
                                            | exact PADT | exact FRsv | exact ST | exact MU | exact WM].
        + cond_cleanup Hlt. assert (X0 : (q7 + - e)%Z = 0%Z) by mlia. try clear Hlt.
          eapply JE0; [exact LIMBS | exact L62 | exact LENC | exact Hlen | exact LIMT | exact LT62 | exact LENT | exact HlenT
                      | exact PADT | exact FRsv | exact ST | exact MU | exact WM].
      - cond_cleanup Hle. assert (Hle' : (0 < q7 + - e)%Z) by mlia. try clear Hle.
        eapply (JCC (q7 + - e)%Z true); [lia | exact LIMBS | exact L62 | exact LENC | exact Hlen | exact LIMT | exact LT62 | exact LENT | exact HlenT
                                          | exact PADT | exact FRsv | exact ST | exact MU | exact WM]. }
    (* [comment removed for export] *)
    assert (J48 : forall (v10 v11 v12 v13 : word),
      evt USEGS POSTC
        (MS (mkR ra SPW gp tp t0 t1 t2 a2 a1 v10 v11 v12 v13 a4 a5 a6 a7
                 a0 (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (- p2)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x26ad4) fc None m0 (seg_rom USEGS))).
    { intros. subst SPW.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Z_to_bv 64 (Z.land ?u 9218868437227405312))] =>
        pose proof (land_range_r u 9218868437227405312 ltac:(lia)) as Hv;
        set (v := Z.land u 9218868437227405312) in * end.
      step. (* [comment removed for export] *) gen_reg (11:reg).
      step. (* [comment removed for export] *)
      if_cases Hz.
      - clear Hz.
        step. (* [comment removed for export] *) rewrite (unsigned_lit v) by lia. rewrite (Z.shiftr_div_pow2 v 52) by lia.
        change (2 ^ 52)%Z with 4503599627370496%Z.
        assert (Hv2 : (0 <= v / 4503599627370496 <= 2047)%Z).
        { split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]. }
        step. (* [comment removed for export] *)
        apply J6c. lia.
      - clear Hz. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        apply J6c. lia. }
    step. (* [comment removed for export] *)
    if_cases Hd.
    - cond_cleanup Hd. rewrite ?signed_lit in Hd by lia.
      step. (* [comment removed for export] *) rewrite uw_add, (swrap32_id (- p2 + 1)) by lia.
      step. (* [comment removed for export] *) trap_dead.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      assert (J28 : forall (sh : Z) (v11 : word), (1 <= sh <= 64)%Z ->
        evt USEGS POSTC
          (MS (mkR ra SPW gp tp t0 t1 t2 a2 a1 (Z_to_bv 64 (- p2 + 1)) v11 (Z_to_bv 64 sh) (Z_to_bv 64 e) a4 a5 a6 a7
                   a0 (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (- p2)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x26ab4) fc None m0 (seg_rom USEGS))).
      { intros sh v11 Hsh. subst SPW.
        step. (* [comment removed for export] *) rewrite ?word_add_lit2.
        step. (* [comment removed for export] *) rewrite ?uw_add2, (swrap32_id (p2 + sh)) by lia.
        step. (* [comment removed for export] *) if_not_taken.
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
        apply J48. }
      step. (* [comment removed for export] *)
      if_cases Hq.
      + cond_cleanup Hq. apply J28. lia.
      + cond_cleanup Hq. step. (* [comment removed for export] *) apply J28. lia.
    - cond_cleanup Hd. rewrite ?signed_lit in Hd by lia.
      step. (* [comment removed for export] *) rewrite Hp2, uw_mod32, (swrap32_id (p2 + 11)) by lia.
      step. (* [comment removed for export] *) trap_dead.
      gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      assert (J00 : forall (v10 v11 v12 : word),
        evt USEGS POSTC
          (MS (mkR ra SPW gp tp t0 t1 t2 a2 a1 v10 v11 v12 (Z_to_bv 64 2047) a4 a5 a6 a7
                   a0 (Z_to_bv 64 e) (Z_to_bv 64 p2) (Z_to_bv 64 (- p2)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x26a8c) fc None m0 (seg_rom USEGS))).
      { intros. subst SPW. gstep. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gen_reg (11:reg). step. (* [comment removed for export] *) apply J48. }
      step. (* [comment removed for export] *)
      if_cases Hq.
      + clear Hq. apply J00.
      + clear Hq. step. (* [comment removed for export] *) apply J00.
  Qed.
End Main.
