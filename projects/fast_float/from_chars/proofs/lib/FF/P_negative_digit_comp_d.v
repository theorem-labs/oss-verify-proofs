(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Plain.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Spf_text ImgFacts Bigint_defs P_pow5_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_pow5_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_memset_stmt P_negative_digit_comp_d_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Spf_text OSSVerify.Proofs.fast_float.from_chars.lib.FF.ImgFacts OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow5_stmt.P_shl_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_memset_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_negative_digit_comp_d_stmt.
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
Ltac gen_val e := let X := fresh "rv" in set (X := e) in *; clearbody X.
Ltac gen_big :=
  repeat match goal with
  | |- context [Some (Z_to_bv 64 (Z.lor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lor a b))
  | |- context [Some (Z_to_bv 64 (Z.land ?a ?b))] => gen_val (Z_to_bv 64 (Z.land a b))
  | |- context [Some (Z_to_bv 64 (Z.lxor ?a ?b))] => gen_val (Z_to_bv 64 (Z.lxor a b))
  | |- context [Some (Z_to_bv 64 (Z.shiftr ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftr a b))
  | |- context [Some (Z_to_bv 64 (Z.shiftl ?a ?b))] => gen_val (Z_to_bv 64 (Z.shiftl a b))
  | |- context [Some (Z_to_bv 64 (Z.mul ?a ?b))] => gen_val (Z_to_bv 64 (Z.mul a b))
  | |- context [Some (Z_to_bv 64 (Z.sub ?a ?b))] => gen_val (Z_to_bv 64 (Z.sub a b))
  | |- context [Some (Z_to_bv 64 (Z.div ?a ?b))] => gen_val (Z_to_bv 64 (Z.div a b))
  | |- context [Some (Z_to_bv 64 (bv_swrap ?n ?b))] => gen_val (Z_to_bv 64 (bv_swrap n b))
  | |- context [Some (Z_to_bv 64 (Z.b2z ?b))] => gen_val (Z_to_bv 64 (Z.b2z b))
  | |- context [Some (Z_to_bv 64 (bv_unsigned ?a + bv_unsigned ?b)%Z)] => gen_val (Z_to_bv 64 (bv_unsigned a + bv_unsigned b)%Z)
  | |- context [Some (zx8 ?a)] => gen_val (zx8 a)
  | |- context [Some (zx16 ?a)] => gen_val (zx16 a)
  | |- context [Some (sx32 ?a)] => gen_val (sx32 a)
  end.
Ltac gstep := step; gen_big.


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

Ltac swrap_unfold_tac :=
  unfold bv_swrap, bv_wrap in *;
  replace (bv_half_modulus 32) with (2^31)%Z in * by reflexivity;
  replace (bv_modulus 32) with (2^32)%Z in * by reflexivity.

(* [comment removed for export] *)
Lemma u64arr_cons : forall m A v ws,
  rw_cells PSEGS m A [C8 v] -> u64arr PSEGS m (A + 8) ws -> u64arr PSEGS m A (v :: ws).
Proof.
  intros m A v ws [[_ Hb] Hw] [Hb2 Hw2]. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  cbn [cells_size csize Nat.add] in Hw.
  split.
  - cbn [u64s map concat]. change (le8 v ++ u64s ws) with (le8 v ++ u64s ws).
    apply (proj2 (bytes_at_app PSEGS m A (le8 v) (u64s ws))). split; [exact Hb|].
    rewrite length_le8. exact Hb2.
  - cbn [length]. rewrite Nat2Z.inj_succ.
    replace (8 * Z.succ (Z.of_nat (length ws)))%Z with (8 + 8 * Z.of_nat (length ws))%Z by lia.
    apply (proj2 (wr_at_app PSEGS m A 8 (8 * Z.of_nat (length ws)) ltac:(lia) ltac:(lia))). split; [exact Hw| exact Hw2].
Qed.


Lemma negw_val : forall e, (-2^30 <= e <= -1)%Z ->
  bv_unsigned (Z_to_bv 64 (bv_swrap 32 (0 - bv_unsigned (Z_to_bv 64 e)))) = (- e)%Z.
Proof.
  intros e He. rewrite !unsigned_lit_wrap. swrap_unfold_tac.
  Z.div_mod_to_equations. lia.
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

Section Main.
  Hypothesis memset_spec : memset_stmt.
  Hypothesis pow5_spec : pow5_stmt.
  Hypothesis shl_spec : shl_stmt.

  #[using="memset_spec pow5_spec shl_spec"] Lemma negative_digit_comp_d_spec : negative_digit_comp_d_stmt.
  Proof. LiaFast.lf_pins (fun (memset_spec pow5_spec shl_spec : LiaFast.U) => LiaFast.u0).
    unfold negative_digit_comp_d_stmt. intros until e. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM Hp2 Rp2 He Re SEP.
    pose proof (munch_refl (negative_digit_comp_d_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [negative_digit_comp_d_W] in MU.
    pose proof (wmono_refl PSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
    subst a3.
    pose proof (u64arr_outside_rodata_P _ _ _ PR LIMBS ltac:(rewrite L62; lia)) as ARO1. rewrite L62 in ARO1.
    pose proof (rw_cells_outside_rodata_P _ _ _ PR LENC ltac:(cbn; lia)) as ARO2. cbn [cells_size csize Nat.add] in ARO2.
    carve_frame 576%nat ST.
    do 10 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    (* [comment removed for export] *)
    assert (J50 : forall (v10 v11 v12 v13 v14 vs4 : word),
      evt PSEGS (negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp t0 t1 t2 a2 a1 v10 v11 v12 v13 v14 a5 a6 a7
                 a0 (Z_to_bv 64 e) vs4 rv rv0 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x25e40) fc None m0 (seg_rom PSEGS))).
    { intros.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- context [Some (Z_to_bv 64 (Z.shiftl ?u 1 + 1)%Z)] =>
        assert (Hs7 : bv_unsigned (Z_to_bv 64 (Z.shiftl u 1 + 1)%Z) <> 0%Z)
          by (rewrite Z.shiftl_mul_pow2 by lia; rewrite !unsigned_lit_wrap;
              pose proof (bv_unsigned_in_range 64 v10) as R10; unfold bv_modulus in R10;
              Z.div_mod_to_equations; lia);
        remember (Z_to_bv 64 (Z.shiftl u 1 + 1)%Z) as s7w eqn:Hs7w; clear Hs7w end.
      gen_big.
      (* [comment removed for export] *)
      eapply (rw_cells_split_CB PSEGS _ _ [] 504 _ _ [8; 496]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
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
      pose proof (rw_cells_of_u8arr PSEGS _ _ _ (conj ZB2 ZW2)) as LENT. clear ZB2 ZW2. rewrite repeat_length in LENT.
      pose proof (rw_cells_of_u8arr PSEGS _ _ _ (conj ZB6 ZW6)) as PADT. clear ZB6 ZW6. rewrite repeat_length in PADT.
      pose proof (rw_cells_of_u8arr PSEGS _ _ _ (conj ZBL ZWL)) as LIML. clear ZBL ZWL. rewrite repeat_length in LIML.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) => rename m' into m2 end.
      destruct (u64arr_of_rw_cells PSEGS _ _ 61 _ LIML) as (wsz & Lz & LIMBT). clear LIML.
      replace (bv_unsigned sp + -568)%Z with (bv_unsigned sp + -576 + 8)%Z in LIMBT by lia.
      pose proof (u64arr_cons _ _ _ _ FR0 LIMBT) as LIMT. clear FR0 LIMBT.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases He0. { cond_cleanup He0. exfalso. Z.div_mod_to_equations. lia. }
      clear He0.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose_sp_lits sp.
      pose proof (negw_val e ltac:(lia)) as UA1.
      replace (bv_unsigned sp + -80)%Z with (bv_unsigned sp + -576 + 496)%Z in LENT by lia.
      assert (LT62 : length (s7w :: wsz) = 62%nat) by (cbn [length]; rewrite Lz; reflexivity).
      assert (NORMT : bnorm (s7w :: wsz) (Z.to_nat 1)).
      { right. cbn. unfold limbZ. cbn. exact Hs7. }
      step. (* [comment removed for export] *)
      call pow5_spec.
      { rewrite_sp_lits sp. replace (bv_unsigned sp + -576 - 1232)%Z with (bv_unsigned sp - 1808)%Z by lia. exact ST. }
      { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
      { rewrite_sp_lits sp. lia. }
      { exact PR. }
      { rewrite_sp_lits sp. exact LIMT. }
      { exact LT62. }
      { rewrite_sp_lits sp. exact LENT. }
      { lia. }
      { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
      { exact NORMT. }
      { rewrite UA1. lia. }
      { rewrite UA1. apply cap_neg; [|lia]. change (Z.to_nat 1) with 1%nat. cbn [bval]. unfold limbZ. cbn [nth].
        pose proof (bv_unsigned_in_range 64 s7w) as R7. unfold bv_modulus in R7. change (2 ^ (64 * Z.of_nat 0))%Z with 1%Z. lia. }
      { rewrite_sp_lits sp. lia. }
      rewrite_sp_lits_all sp. rewrite -> ?UA1 in *.
      clear LT62 NORMT UA1. rename MI into STp. rename PC into LIMT. rename PC0 into LT62. rename PC1 into LENT.
      rename PC2 into HlenT. clear PC3 PC4. try clear PR. rename POST into PR.
      lazymatch type of LIMT with u64arr _ ?mq _ ?wq => rename mq into m3; rename wq into wst end.
      lazymatch type of HlenT with (0 <= ?l <= 62)%Z => rename l into lent end.
      rename STp into ST. replace (bv_unsigned sp + -576 - 1232)%Z with (bv_unsigned sp - 1808)%Z in ST by lia.
      (* [comment removed for export] *)
      assert (JA0 : forall (m4 : word -> option byte) (wsr wst' : list word) (lenr lent' : Z)
                           (v1 v5 v6 v7 v10 v11 v12 v13 v14 v15 v16 v17 v20 v28 v29 v30 v31 : word),
        u64arr PSEGS m4 (bv_unsigned a0) wsr -> length wsr = 62%nat ->
        rw_cells PSEGS m4 (bv_unsigned a0 + 496) [C2 (Z_to_bv 64 lenr)] -> (0 <= lenr <= 62)%Z ->
        u64arr PSEGS m4 (bv_unsigned sp + -576) wst' -> length wst' = 62%nat ->
        rw_cells PSEGS m4 (bv_unsigned sp + -576 + 496) [C2 (Z_to_bv 64 lent')] -> (0 <= lent' <= 62)%Z ->
        rw_cells PSEGS m4 (bv_unsigned sp + -78) [CB 6 (repeat (Z_to_bv 8 0) 6)] ->
        rw_cells PSEGS m4 (bv_unsigned sp + -72) [C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
        stk PSEGS m4 (bv_unsigned sp - 1808) (bv_unsigned sp + -576) ->
        pristine m4 65536 139264 ->
        munch [((bv_unsigned sp - 1808)%Z, bv_unsigned sp); (bv_unsigned a0, (bv_unsigned a0 + 498)%Z)] m m4 ->
        wmono PSEGS m m4 ->
        evt PSEGS (negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
          (MS (mkR v1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp v5 v6 v7 a2 a1 v10 v11 v12 v13 v14 v15 v16 v17
                   a0 (Z_to_bv 64 e) v20 rv rv0 s7w s8 s9 s10 s11 v28 v29 v30 v31)
              F (Z_to_bv 64 0x25e90) fc None m4 (seg_rom PSEGS))).
      { intros m4 wsr wst' lenr lent' v1 v5 v6 v7 y10 y11 y12 y13 y14 y15 y16 y17 v20 v28 v29 v30 v31
               LIR LR LER HLR LIT LT LET HLT PAD SAV ST4 PR4 MU4 WM4.
        clear LIMT LT62 LENT HlenT PADT FRsv PR MU WM Lz wsz.
        replace (bv_unsigned sp + -576 + 496)%Z with (bv_unsigned sp + -80)%Z in LET by lia.
        (* [comment removed for export] *)
        assert (JBC : forall u10 u11 u12 u13 u14 u15 u18 : word,
          evt PSEGS (negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
            (MS (mkR v1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp v5 v6 v7 a2 a1 u10 u11 u12 u13 u14 u15 y16 y17
                     u18 (Z_to_bv 64 e) v20 rv rv0 s7w s8 s9 s10 s11 v28 v29 v30 v31)
                F (Z_to_bv 64 0x25eac) fc None m4 (seg_rom PSEGS))).
        { intros.
          assert (J58 : forall w9 w10 w11 w12 w13 w14 : word,
            evt PSEGS (negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
              (MS (mkR v1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp v5 v6 v7 a2 w9 w10 w11 w12 w13 w14 u15 y16 y17
                       u18 (Z_to_bv 64 e) v20 rv rv0 s7w s8 s9 s10 s11 v28 v29 v30 v31)
                  F (Z_to_bv 64 0x25f48) fc None m4 (seg_rom PSEGS))).
          { intros.
            do 3 gstep. (* [comment removed for export] *)
            do 9 step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            pose proof (rw_cells_of_u64arr PSEGS _ _ _ LIT) as OBJ. rewrite LT in OBJ. clear LIT.
            chunk_join OBJ LET FRa. chunk_join FRa PAD FRb. chunk_join FRb SAV FR.
            release_frame FR ST4 (bv_unsigned sp).
            unfold negative_digit_comp_d_post. finish.
            all: try eassumption. all: try lia. }
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hden.
          - clear Hden. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            assert (J30 : forall w12 w13 : word,
              evt PSEGS (negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
                (MS (mkR v1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp v5 v6 v7 a2 a1 u10 u11 w12 w13 (Z_to_bv 64 64) u15 y16 y17
                         u18 (Z_to_bv 64 e) v20 rv rv0 s7w s8 s9 s10 s11 v28 v29 v30 v31)
                    F (Z_to_bv 64 0x25f20) fc None m4 (seg_rom PSEGS))).
            { intros. do 10 gstep. (* [comment removed for export] *) apply J58. }
            if_cases Hb; [clear Hb; apply J30 | clear Hb; step; (* [comment removed for export] *) apply J30].
          - clear Hden. (* [comment removed for export] *)
            do 10 gstep. (* [comment removed for export] *)
            do 2 gstep. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            gstep. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            if_cases Hinf.
            + clear Hinf. step. step. step. gstep. step. (* [comment removed for export] *) apply J58.
            + clear Hinf. step. (* [comment removed for export] *) step. step. step. gstep. step. apply J58. }
        (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        rewrite !zx16_lit_small by lia.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hl1.
        { clear Hl1. step. (* [comment removed for export] *) apply JBC. }
        cond_cleanup Hl1.
        step. (* [comment removed for export] *)
        if_cases Hl2.
        2:{ clear Hl2. step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply JBC. }
        cond_cleanup Hl2.
        assert (HLEQ : lenr = lent') by lia. subst lent'. clear Hl1 Hl2.
        (* [comment removed for export] *)
        pose proof (u64arr_bound _ _ _ _ LIR) as BR. rewrite LR in BR.
        pose proof (u64arr_bound _ _ _ _ LIT) as BT. rewrite LT in BT.
        assert (CL : forall (n : nat) (u10 u11 u14 u15 : word), (Z.of_nat n <= lenr)%Z ->
          evt PSEGS (negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
            (MS (mkR v1 (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp v5 v6 v7 a2 a1 u10 u11
                     (Z_to_bv 64 (bv_unsigned sp + -576 + 8 * Z.of_nat n - 8)) (Z_to_bv 64 (Z.of_nat n + 1)) u14 u15 y16 y17
                     (Z_to_bv 64 (bv_unsigned a0 + 8 * Z.of_nat n - 8)) (Z_to_bv 64 e) v20 rv rv0 s7w s8 s9 s10 s11 v28 v29 v30 v31)
                F (Z_to_bv 64 0x25f98) fc None m4 (seg_rom PSEGS))).
        { induction n as [|n IH]; intros u10 u11 u14 u15 Hn.
          - step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            if_cases Hz; [clear Hz | cond_cleanup Hz; exfalso; lia].
            step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply JBC.
          - step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            if_cases Hz; [cond_cleanup Hz; exfalso; lia | clear Hz].
            pose proof (u64arr_read PSEGS m4 _ wsr (Z.of_nat n) (nth n wsr w0) (wa (bv_unsigned a0 + 8 * Z.of_nat n)) LIR
                          ltac:(rewrite Nat2Z.id; apply nth_error_nth'; lia) ltac:(lia) eq_refl) as RD1.
            pose proof (u64arr_read PSEGS m4 _ wst' (Z.of_nat n) (nth n wst' w0) (wa (bv_unsigned sp + -576 + 8 * Z.of_nat n)) LIT
                          ltac:(rewrite Nat2Z.id; apply nth_error_nth'; lia) ltac:(lia) eq_refl) as RD2.
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            clear RD1 RD2.
            step. (* [comment removed for export] *)
            if_cases Hgt; [clear Hgt; apply JBC | clear Hgt].
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            step. (* [comment removed for export] *)
            if_cases Hge.
            + clear Hge. goto (apply (IH u10)). lia.
            + clear Hge. step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply JBC. }
        step. (* [comment removed for export] *)
        rewrite (Z.shiftl_mul_pow2 _ 3) by lia. change (2 ^ 3)%Z with 8%Z.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        goto (apply (CL (Z.to_nat lenr))). all: lia. }
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hle.
      - clear Hle.
        step. (* [comment removed for export] *)
        if_cases Hlt.
        + clear Hlt.
          gstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          pose_sp_lits sp.
          destruct (stk_split _ _ _ (bv_unsigned sp + -576 - 32)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
          step. (* [comment removed for export] *)
          call shl_spec.
          { rewrite_sp_lits sp. exact SThi. }
          { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
          { exact LIMBS. } { exact L62. } { exact LENC. } { exact Hlen. } { exact A8. }
          { rewrite_sp_lits sp. lia. }
          rewrite_sp_lits_all sp.
          step. (* [comment removed for export] *)
          pose proof (stk_merge _ _ _ _ _ STlo MI ltac:(lia)) as ST4.
          eapply JA0; [exact PC | exact PC0 | exact PC1 | exact PC2 | exact LIMT | exact LT62 | exact LENT | exact HlenT
                      | exact PADT | exact FRsv | exact ST4 | exact PR | exact MU | exact WM].
        + clear Hlt.
          eapply JA0; [exact LIMBS | exact L62 | exact LENC | exact Hlen | exact LIMT | exact LT62 | exact LENT | exact HlenT
                      | exact PADT | exact FRsv | exact ST | exact PR | exact MU | exact WM].
      - clear Hle.
        step. (* [comment removed for export] *)
        pose_sp_lits sp.
        destruct (stk_split _ _ _ (bv_unsigned sp + -576 - 32)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
        step. (* [comment removed for export] *)
        call shl_spec.
        { rewrite_sp_lits sp. exact SThi. }
        { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
        { rewrite_sp_lits sp. exact LIMT. } { exact LT62. } { rewrite_sp_lits sp. exact LENT. } { exact HlenT. }
        { rewrite_sp_lits sp. Z.div_mod_to_equations. lia. }
        { rewrite_sp_lits sp. lia. }
        rewrite_sp_lits_all sp.
        step. (* [comment removed for export] *)
        pose proof (stk_merge _ _ _ _ _ STlo MI ltac:(lia)) as ST4.
        eapply JA0; [exact LIMBS | exact L62 | exact LENC | exact Hlen | exact PC | exact PC0 | exact PC1 | exact PC2
                    | exact PADT | exact FRsv | exact ST4 | exact PR | exact MU | exact WM]. }
    (* [comment removed for export] *)
    assert (J18 : forall v11 v12 v13 v14 : word,
      evt PSEGS (negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
        (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp t0 t1 t2 a2 a1 (Z_to_bv 64 4503599627370495) v11 v12 v13 v14 a5 a6 a7
                 a0 (Z_to_bv 64 e) s4 rv rv0 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x25e08) fc None m0 (seg_rom PSEGS))).
    { intros.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hz.
      - clear Hz. gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J50.
      - clear Hz. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J50. }
    step. (* [comment removed for export] *)
    if_cases Hd.
    - clear Hd. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (J00 : forall w11 w12 : word,
        evt PSEGS (negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp t0 t1 t2 a2 a1 (Z_to_bv 64 4503599627370495) w11 w12 (Z_to_bv 64 64) a4 a5 a6 a7
                   a0 (Z_to_bv 64 e) s4 rv rv0 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x25df0) fc None m0 (seg_rom PSEGS))).
      { intros. do 6 gstep. (* [comment removed for export] *) apply J18. }
      if_cases Hb; [clear Hb; apply J00 | clear Hb; step; (* [comment removed for export] *) apply J00].
    - clear Hd. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (Jdc : forall w11 w12 w13 w14 : word,
        evt PSEGS (negative_digit_comp_d_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
          (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -576)) gp tp t0 t1 t2 a2 a1 (Z_to_bv 64 4503599627370495) w11 w12 w13 w14 a5 a6 a7
                   a0 (Z_to_bv 64 e) s4 rv rv0 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x25dcc) fc None m0 (seg_rom PSEGS))).
      { intros. gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J18. }
      if_cases Hb; [clear Hb; apply Jdc | clear Hb; gstep; (* [comment removed for export] *) apply Jdc].
  Qed.
End Main.
