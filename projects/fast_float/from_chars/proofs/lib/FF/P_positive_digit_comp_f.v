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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Bigint_defs P_pow10_stmt P_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_hi64_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require P_positive_digit_comp_f_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FF.Bigint_defs OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_pow10_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_hi64_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_hi64_stmt.P_ctlz_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FF.P_positive_digit_comp_f_stmt.
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

Lemma cb1_c1 : forall m A l, rw_cells PSEGS m A [CB 1 l] -> exists b, rw_cells PSEGS m A [C1 b].
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
    unfold positive_digit_comp_f_stmt. intros until len. intros ST AL SPLO PR LIMBS L62 LENC Hlen A8 NORM He CAP SEP.
    pose proof (munch_refl (positive_digit_comp_f_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [positive_digit_comp_f_W] in MU.
    pose proof (wmono_refl PSEGS m) as WM.
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
    destruct (stk_split _ _ _ (bv_unsigned sp + -32 - 1264)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
    step. (* [comment removed for export] *)
    call pow10_spec.
    1:{ rewrite ULs. exact SThi. }
    1:{ rewrite ULs. Z.div_mod_to_equations. lia. }
    1:{ rewrite ULs. lia. }
    1:{ exact PR. } 1:{ exact LIMBS. } 1:{ exact L62. } 1:{ exact LENC. } 1:{ exact Hlen. } 1:{ exact A8. } 1:{ exact NORM. }
    1:{ exact He. } 1:{ exact CAP. }
    1:{ rewrite ULs. lia. }
    rewrite ?ULs in *.
    clear CAP NORM.
    rename MI into SThi. rename PC into LIMBS. rename PC0 into L62'. rename PC1 into LENC. rename PC2 into Hlen'. clear PC3. rename PC4 into NORM. rename POST into PR'.
    try clear PR.
    lazymatch type of LIMBS with u64arr _ ?mq _ ?wq => rename mq into m1; rename wq into ws1 end.
    lazymatch type of Hlen' with (0 <= ?l <= 62)%Z => rename l into len1 end.
    (* [comment removed for export] *)
    eapply (rw_cells_split_CB PSEGS m1 _ [] 8 _ _ [7; 1]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    chunk_split FR 1%nat FR7 FRr. chunk_split FRr 1%nat TB FRs.
    destruct (cb1_c1 _ _ _ TB) as [tb TB1]. clear TB.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -25) ltac:(lia)) as UL7.
    pose proof (stk_merge _ _ _ _ _ STlo SThi ltac:(lia)) as ST. clear STlo SThi.
    destruct (stk_split _ _ _ (bv_unsigned sp + -32 - 16)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
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
    assert (EPI : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt PSEGS (positive_digit_comp_f_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28e18) fc None m3 (seg_rom PSEGS))).
    { intros.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      chunk_join FR7 TB FRa. chunk_join FRa FRs FR.
      release_frame FR ST (bv_unsigned sp).
      unfold positive_digit_comp_f_post. finish.
      all: try eassumption. all: try lia. }
    assert (J1c : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt PSEGS (positive_digit_comp_f_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28e0c) fc None m3 (seg_rom PSEGS))).
    { intros. do 3 gstep. apply EPI. }
    assert (J78 : forall x1 x5 x6 x7 x8 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word,
      evt PSEGS (positive_digit_comp_f_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 a0 x10 x11 x12 x13 x14 x15 x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x28d68) fc None m3 (seg_rom PSEGS))).
    { intros. do 10 gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      - clear Hq. step. gstep. gstep. step. (* [comment removed for export] *) apply EPI.
      - clear Hq. step. (* [comment removed for export] *) step. gstep. gstep. step. apply EPI. }
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    gstep. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hden.
    - (* [comment removed for export] *)
      clear Hden.
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      assert (Jcc : forall x1 x5 x6 x7 x8 x10 x11 x12 x14 x15 x16 x17 x28 x29 x30 x31 : word,
        evt PSEGS (positive_digit_comp_f_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) m)
          (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp x5 x6 x7 x8 a0 x10 x11 x12 (Z_to_bv 64 64) x14 x15 x16 x17
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x28dbc) fc None m3 (seg_rom PSEGS))).
      { intros.
        do 13 gstep. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hb1. { clear Hb1. apply J1c. }
        clear Hb1.
        step. (* [comment removed for export] *)
        if_cases Hb2.
        + clear Hb2. do 4 gstep. apply J1c.
        + clear Hb2. step. (* [comment removed for export] *)
          if_cases Hb3.
          * clear Hb3. apply J1c.
          * clear Hb3. do 4 gstep. apply J1c. }
      if_cases Hsh.
      + clear Hsh. apply Jcc.
      + clear Hsh. step. (* [comment removed for export] *) apply Jcc.
    - (* [comment removed for export] *)
      clear Hden.
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb1. { clear Hb1. apply J78. }
      clear Hb1.
      step. (* [comment removed for export] *)
      gstep. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb2.
      + clear Hb2. do 6 gstep. apply J78.
      + clear Hb2. step. (* [comment removed for export] *)
        if_cases Hb3.
        * clear Hb3. apply J78.
        * clear Hb3. do 6 gstep. apply J78.
  Qed.
End Main.
