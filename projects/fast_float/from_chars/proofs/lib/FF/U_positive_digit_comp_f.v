(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.fast_float.from_chars.images Require Import Ubsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs Wbig_tac Wdc_tac U_pow10_stmt U_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require U_positive_digit_comp_f_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wbig_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.Wdc_tac OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_pow10_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_hi64_stmt.U_ctlz_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.U_positive_digit_comp_f_stmt.
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

Lemma cb1_c1 : forall m A l, rw_cells USEGS m A [CB 1 l] -> exists b, rw_cells USEGS m A [C1 b].
Proof.
  intros m A l [[Hwf Hb] Hw]. cbn in Hwf. destruct Hwf as [Hl _].
  destruct l as [|b [|]]; cbn in Hl; try discriminate.
  exists b. split; [split|]; [cbn; tauto | exact Hb | exact Hw].
Qed.

Section Main.
  Hypothesis pow10_spec : pow10_stmt.
  Hypothesis hi64_spec : hi64_stmt.
  Hypothesis ctlz_spec : ctlz_stmt.

  #[using="pow10_spec hi64_spec ctlz_spec"] Lemma positive_digit_comp_f_spec : positive_digit_comp_f_stmt.
  Proof. LiaFast.lf_pins (fun (pow10_spec hi64_spec ctlz_spec : LiaFast.U) => LiaFast.u0).
    unfold positive_digit_comp_f_stmt. intros until len. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NZ NORM He CAP SEP.
    pose proof (munch_refl (positive_digit_comp_f_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [positive_digit_comp_f_W] in MU.
    pose proof (wmono_refl USEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
    carve_frame 32%nat ST.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
    destruct (stk_split _ _ _ (bv_unsigned sp + -32 - 1328)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
    step. (* [comment removed for export] *)
    call pow10_spec.
    1:{ rewrite ULs. exact SThi. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. } 1:{ exact A8. } 1:{ exact NZ. } 1:{ exact NORM. }
    1:{ exact He. } 1:{ exact CAP. }
    1:{ rewrite ULs. lia. }
    rewrite ?ULs in *.
    clear CAP NORM.
    rename MI into SThi. rename PC into LIMBS. rename PC0 into L62'. rename PC1 into LENC. rename PC2 into Hlen'. clear PC3. rename PC4 into NORM. rename POST into PR'.
    try clear PR.
    lazymatch type of LIMBS with u64arr _ ?mq _ ?wq => rename mq into m1; rename wq into ws1 end.
    lazymatch type of Hlen' with (0 <= ?l <= 62)%Z => rename l into len1 end.
    (* [comment removed for export] *)
    eapply (rw_cells_split_CB USEGS m1 _ [] 8 _ _ [7; 1]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    chunk_split FR 1%nat FR7 FRr. chunk_split FRr 1%nat TB FRs.
    destruct (cb1_c1 _ _ _ TB) as [tb TB1]. clear TB.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -25) ltac:(lia)) as UL7.
    pose proof (stk_merge _ _ _ _ _ STlo SThi ltac:(lia)) as ST. clear STlo SThi.
    destruct (stk_split _ _ _ (bv_unsigned sp + -32 - 32)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
    step. (* [comment removed for export] *)
    call hi64_spec.
    1:{ exact LIMBS. } 1:{ exact L62'. } 1:{ exact LENC. } 1:{ exact Hlen'. } 1:{ exact NORM. }
    1:{ rewrite UL7. exact TB1. }
    1:{ rewrite ULs. exact SThi. }
    1:{ exact PR'. }
    1:{ rewrite ULs. lia. }
    1:{ rewrite ULs. lia. }
    1:{ rewrite UL7, ULs. lia. }
    1:{ rewrite UL7. lia. }
    rewrite ?ULs, ?UL7 in *.
    rename MI into Ht. rename PC into TB. rename POST into SThi.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
    pose proof (stk_merge _ _ _ _ _ STlo SThi ltac:(lia)) as ST. clear STlo SThi.
    destruct (stk_split _ _ _ (bv_unsigned sp + -32 - 16)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    call ctlz_spec.
    1:{ exact LIMBS. } 1:{ exact L62'. } 1:{ exact LENC. } 1:{ exact Hlen'. } 1:{ exact NORM. }
    1:{ rewrite ULs. exact SThi. }
    1:{ exact PR'. }
    1:{ rewrite ULs. lia. }
    1:{ rewrite ULs. lia. }
    rewrite ?ULs in *.
    rename MI into Hz. rename POST into SThi2.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m3 end.
    pose proof (stk_merge _ _ _ _ _ STlo SThi2 ltac:(lia)) as ST. clear STlo SThi2.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let p := eval vm_compute in (bv_key (10:reg)) in
      let v := eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end) in
      lazymatch v with Z_to_bv 64 ?z => rename z into zc end end.
    step. (* [comment removed for export] *) rewrite (zx16_lit len1) by lia.
    step. (* [comment removed for export] *) rewrite (unsigned_lit len1) by lia. rewrite (Z.shiftl_mul_pow2 len1 6) by lia. change (2^6)%Z with 64%Z.
    step. (* [comment removed for export] *) rewrite word_sub_lit2.
    step. (* [comment removed for export] *) rewrite uw_sub2. rewrite (swrap32_id (len1 * 64 - zc)) by lia.
    step. (* [comment removed for export] *) if_not_taken.
    step. (* [comment removed for export] *) rewrite uw_add, Z.add_0_r. rewrite (swrap32_id (len1 * 64 - zc)) by lia.
    step. (* [comment removed for export] *) rewrite uw_add. rewrite (swrap32_id (len1 * 64 - zc + -64)) by lia.
    step. (* [comment removed for export] *) trap_dead.
    step. (* [comment removed for export] *) rewrite uw_add. rewrite (swrap32_id (len1 * 64 - zc + -64 + 150)) by lia.
    step. (* [comment removed for export] *) trap_dead.
    set (P := (len1 * 64 - zc + 86)%Z) in *.
    assert (HP : (-170 <= P <= 4054)%Z) by (subst P; lia).
    step. (* [comment removed for export] *) rewrite (zxb_lit8 x13) by lia.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) trap_dead.
    step. (* [comment removed for export] *) rewrite uw_sub. rewrite (swrap32_id (0 - P)) by lia.
    step. (* [comment removed for export] *) rewrite ?word_sub_lit2, ?word_sub_lit.
    step. (* [comment removed for export] *) if_not_taken.
    step. (* [comment removed for export] *)
    (* [comment removed for export] *)
    set (POSTC := positive_digit_comp_f_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m).
    set (SPW := Z_to_bv 64 (bv_unsigned sp + -32)).
    assert (EPI : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt USEGS POSTC
        (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2ab18) fc None m3 (seg_rom USEGS))).
    { intros. subst POSTC SPW.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      chunk_join FR7 TB FRa. chunk_join FRa FRs FR.
      release_frame FR ST (bv_unsigned sp).
      unfold positive_digit_comp_f_post. finish.
      all: try eassumption. all: try lia. }
    assert (J5c : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt USEGS POSTC
        (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2ab10) fc None m3 (seg_rom USEGS))).
    { intros. subst SPW. do 2 gstep. apply EPI. }
    assert (J4c : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt USEGS POSTC
        (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2ab00) fc None m3 (seg_rom USEGS))).
    { intros. subst SPW. do 4 gstep. apply J5c. }
    assert (J24 : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt USEGS POSTC
        (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2aad8) fc None m3 (seg_rom USEGS))).
    { intros. subst SPW. step. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      - clear Hq. gstep. gstep. step. apply J5c.
      - clear Hq. step. (* [comment removed for export] *) gstep. gstep. step. apply J5c. }
    assert (Jf8 : forall (q : Z) (x1 x5 x6 x7 x8 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      (-2^20 <= q <= 2^20)%Z ->
      evt USEGS POSTC
        (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 (Z_to_bv 64 q) x12 x13 x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2aaac) fc None m3 (seg_rom USEGS))).
    { intros q. intros. subst SPW.
      gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      - clear Hq. step. (* [comment removed for export] *) rewrite uw_add. rewrite (swrap32_id (q + 1)) by lia.
        step. (* [comment removed for export] *) trap_dead.
        step. (* [comment removed for export] *) step. (* [comment removed for export] *) apply J24.
      - clear Hq. gstep. gstep. step. (* [comment removed for export] *) apply J24. }
    step. (* [comment removed for export] *)
    if_cases Hd.
    - (* [comment removed for export] *)
      cond_cleanup Hd. rewrite ?signed_lit in Hd by lia.
      step. (* [comment removed for export] *) rewrite uw_add. rewrite (swrap32_id (0 - P + 1)) by lia.
      step. (* [comment removed for export] *) trap_dead.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (J8c : forall (sh : Z) (x1 x5 x6 x7 x8 x10 x14 x15 x16 x17 x28 x29 x30 x31 : word),
        (1 <= sh <= 64)%Z ->
        evt USEGS POSTC
          (MS (mkR x1 SPW gp tp x5 x6 x7 x8 a0 x10 (Z_to_bv 64 sh) (Z_to_bv 64 P) (Z_to_bv 64 (0 - P + 1)) x14 x15 x16 x17
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x2aa40) fc None m3 (seg_rom USEGS))).
      { intros sh. intros. subst SPW.
        step. (* [comment removed for export] *) rewrite ?word_add_lit2.
        step. (* [comment removed for export] *) rewrite ?uw_add2. rewrite (swrap32_id (P + sh)) by lia.
        step. (* [comment removed for export] *) if_not_taken.
        gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        gstep. (* [comment removed for export] *)
        do 10 gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb1. { clear Hb1. apply J4c. }
        clear Hb1. gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb2.
        + clear Hb2. step. (* [comment removed for export] *)
          if_cases Hb3. { clear Hb3. apply J4c. }
          clear Hb3. gstep. gstep. apply J4c.
        + clear Hb2. step. (* [comment removed for export] *)
          if_cases Hb3. { clear Hb3. step. step. apply J4c. }
          clear Hb3. gstep. (* [comment removed for export] *) step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          if_cases Hb4. { clear Hb4. gstep. gstep. apply J4c. }
          clear Hb4. step. (* [comment removed for export] *) apply J4c. }
      step. (* [comment removed for export] *)
      if_cases Hs.
      + cond_cleanup Hs. apply J8c. lia.
      + cond_cleanup Hs. step. (* [comment removed for export] *) apply J8c. lia.
    - (* [comment removed for export] *)
      cond_cleanup Hd. rewrite ?signed_lit in Hd by lia.
      step. (* [comment removed for export] *) rewrite uw_add. rewrite (swrap32_id (P + 40)) by lia.
      step. (* [comment removed for export] *) trap_dead.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb1. { clear Hb1. apply Jf8. lia. }
      clear Hb1.
      gstep. (* [comment removed for export] *) step. (* [comment removed for export] *) gstep. (* [comment removed for export] *) gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb2.
      + clear Hb2. step. (* [comment removed for export] *)
        if_cases Hb3. { clear Hb3. apply Jf8. lia. }
        clear Hb3. gstep. gstep. apply Jf8. lia.
      + clear Hb2. step. (* [comment removed for export] *)
        if_cases Hb3. { clear Hb3. step. step. apply Jf8. lia. }
        clear Hb3. gstep. (* [comment removed for export] *) step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb4. { clear Hb4. gstep. gstep. apply Jf8. lia. }
        clear Hb4. step. (* [comment removed for export] *) apply Jf8. lia.
  Qed.
End Main.
