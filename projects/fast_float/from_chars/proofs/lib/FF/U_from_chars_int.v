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
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Wbig_tac U_from_chars_int_stmt.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Fixpoint image_u8s (A : Z) (n : nat) : list Z :=
  match n with O => [] | S n' => match image_bytes USEGS A 1 with Some [b] => bv_unsigned b | _ => 0%Z end :: image_u8s (A + 1) n' end.
Definition DIGTAB : list Z := Eval vm_compute in (image_u8s 0x15db8 256).
Lemma DIGTAB_ok : table_b USEGS 0x15db8 1 (fun v => [Z_to_bv 8 v]) DIGTAB = true.
Proof. vm_compute. reflexivity. Qed.
Lemma DIGTAB_len : length DIGTAB = 256%nat.
Proof. reflexivity. Qed.

Ltac show_regs :=
    lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ ?mm _) =>
      idtac "pc=" pc "mem=" mm;
      let pr k := let p := eval vm_compute in (bv_key k) in
                  let v := eval cbv beta iota delta [tget mkR] in (match tget p R with Some v => v | None => w0 end) in idtac k ":=" v in
      pr (1:reg); pr (5:reg); pr (6:reg); pr (7:reg); pr (10:reg); pr (11:reg); pr (12:reg); pr (13:reg); pr (14:reg); pr (15:reg); pr (16:reg); pr (17:reg);
      pr (28:reg); pr (29:reg); pr (30:reg); pr (31:reg);
      pr (8:reg); pr (9:reg); pr (18:reg); pr (19:reg); pr (20:reg); pr (21:reg); pr (22:reg); pr (23:reg); pr (24:reg); pr (25:reg); pr (26:reg); pr (27:reg)
    end.

Section Proof.
  (* [comment removed for export] *)
  Variables (ra sp gp tp a0 a1 a2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m m1 : word -> option byte) (bs : list byte) (rold : word) (junk0 : list byte).
  Hypothesis LEN : (Z.of_nat (length bs) = bv_unsigned a1 - bv_unsigned a0)%Z.
  Hypothesis LE : (bv_unsigned a0 <= bv_unsigned a1)%Z.
  Hypothesis NZ : (0 < bv_unsigned a0)%Z.
  Hypothesis SEP1 : (bv_unsigned a2 + 4 <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned a2)%Z.
  Hypothesis SEP2 : (bv_unsigned sp <= bv_unsigned a2 \/ bv_unsigned a2 + 4 <= bv_unsigned sp - 112)%Z.
  Hypothesis SEP3 : (bv_unsigned sp <= bv_unsigned a0 \/ bv_unsigned a1 <= bv_unsigned sp - 112)%Z.
  Hypothesis RO2 : (bv_unsigned a2 + 4 <= 0x10000 \/ 0x22000 <= bv_unsigned a2)%Z.
  Hypothesis RO3 : (0x22000 <= bv_unsigned sp - 112)%Z.
  Hypothesis Ra1 : (bv_unsigned a1 < 2^64)%Z.
  Hypothesis Rsp : (bv_unsigned sp < 2^64)%Z.
  (* [comment removed for export] *)
  Notation FRCELLS cw := [cw; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Hypothesis FR : rw_cells USEGS m1 (bv_unsigned sp + -112) (FRCELLS (CB 8 junk0)).
  Hypothesis OBJ : rw_cells USEGS m1 (bv_unsigned a2) [C4 rold].
  Hypothesis DATA : bytes_at USEGS m1 (bv_unsigned a0) bs.
  Hypothesis PR : pristine m1 0x10000 0x22000.
  Hypothesis ST : stk USEGS m1 (bv_unsigned sp + -112) (bv_unsigned sp + -112).
  Hypothesis MU : munch (from_chars_int_W sp a2) m m1.
  Hypothesis WM : wmono USEGS m m1.

  Notation W := (from_chars_int_W sp a2).
  Ltac fin := finish; try match goal with H : rw_cells _ _ _ [C4 _] |- rw_cells _ _ _ [C4 _] => exact H end.
  Notation POST := (from_chars_int_post_hw ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a2 m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -112)).

  (* [comment removed for export] *)
  Definition M2 (m' : word -> option byte) (cw r : word) : Prop :=
    rw_cells USEGS m' (bv_unsigned sp + -112) (FRCELLS (C8 cw))
    /\ rw_cells USEGS m' (bv_unsigned a2) [C4 r]
    /\ bytes_at USEGS m' (bv_unsigned a0) bs
    /\ pristine m' 0x10000 0x22000
    /\ stk USEGS m' (bv_unsigned sp + -112) (bv_unsigned sp + -112)
    /\ munch W m m' /\ wmono USEGS m m'.

  (* [comment removed for export] *)
  #[using="bs"] Lemma exit_ec : forall (c0w : cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (m' : word -> option byte) (r' : word),
      csize c0w = 8%nat ->
      rw_cells USEGS m' (bv_unsigned sp + -112) (FRCELLS c0w) ->
      rw_cells USEGS m' (bv_unsigned a2) [C4 r'] ->
      stk USEGS m' (bv_unsigned sp + -112) (bv_unsigned sp + -112) ->
      munch W m m' -> wmono USEGS m m' ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2b1d4) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (bs : LiaFast.U) => LiaFast.u0).
    intros until r'. intros Hc FR' OBJ' ST' MU' WM'.
    destruct c0w; cbn in Hc; try discriminate.
    - step. (* [comment removed for export] *)
      do 13 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      release_frame FR' ST' (bv_unsigned sp).
      unfold from_chars_int_post_hw. fin.
    - subst n.
      step. do 13 step. step. step.
      release_frame FR' ST' (bv_unsigned sp).
      unfold from_chars_int_post_hw. fin.
  Qed.

  #[using="bs"] Lemma exit_e8 : forall (c0w : cell) (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (m' : word -> option byte) (r' : word),
      csize c0w = 8%nat ->
      rw_cells USEGS m' (bv_unsigned sp + -112) (FRCELLS c0w) ->
      rw_cells USEGS m' (bv_unsigned a2) [C4 r'] ->
      stk USEGS m' (bv_unsigned sp + -112) (bv_unsigned sp + -112) ->
      munch W m m' -> wmono USEGS m m' ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2b1d0) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (bs : LiaFast.U) => LiaFast.u0).
    intros until r'. intros Hc FR' OBJ' ST' MU' WM'.
    step. (* [comment removed for export] *)
    eapply exit_ec; eassumption.
  Qed.

  (* [comment removed for export] *)
  #[using="a1 LEN SEP1 SEP2 SEP3 RO2 RO3"] Lemma exit_sw : forall (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 a2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2b1c8) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (a1 LEN SEP1 SEP2 SEP3 RO2 RO3 : LiaFast.U) => LiaFast.u0).
    intros until r'. intros (FR' & OBJ' & DATA' & PR' & ST' & MU' & WM').
    unfold from_chars_int_W in MU'.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    eapply (exit_e8 (C8 cw)); try eassumption. reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp"] Lemma L_digits : forall (sd pe x1 x5 x6 x8 x10 x11 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word)
      (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= bv_unsigned pe)%Z -> (bv_unsigned pe <= bv_unsigned a1)%Z ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 pe x8 cw x10 x11 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 (Z_to_bv 64 10) x29 x30 x31)
            F (Z_to_bv 64 0x2b0dc) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp : LiaFast.U) => LiaFast.u0).
    intros until r'. intros HM H1 H2 H3. pose proof HM as HM'. destruct HM as (FR' & OBJ' & DATA' & PR' & ST' & MU' & WM').
    pose proof (bytes_at_bound _ _ _ _ DATA') as Bd.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    unfold FCI_OPT2.
    do 8 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_false.
    do 4 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_false.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    { clear B1. eapply (exit_e8 (C8 cw)); try eassumption. reflexivity. }
    cond_cleanup B1.
    step. (* [comment removed for export] *)
    if_cases B2.
    - clear B2.
      do 5 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B3. { clear B3. eapply (exit_e8 (C8 cw)); try eassumption. reflexivity. }
      clear B3. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      if_cases B4. { clear B4. eapply exit_sw; exact HM'. }
      clear B4. step. (* [comment removed for export] *) step. (* [comment removed for export] *) eapply exit_sw; exact HM'.
    - cond_cleanup B2.
      do 3 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_false.
      do 3 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_false.
      destruct (nth_error bs (Z.to_nat (bv_unsigned sd - bv_unsigned a0))) as [c|] eqn:Hc.
      2:{ exfalso. apply nth_error_None in Hc. lia. }
      pose proof (u8ro_read USEGS m' (bv_unsigned a0) bs (bv_unsigned sd - bv_unsigned a0) c _ DATA' Hc ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. cbn in Rc.
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      pose proof (table_read USEGS _ _ _ _ m' _ _ DIGTAB_ok PR' ltac:(lia) ltac:(rewrite DIGTAB_len; cbn; lia)
                    (bv_unsigned (zxb c)) ltac:(unfold zxb; rewrite unsigned_lit by lia; rewrite DIGTAB_len; lia)) as RD.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B5. { clear B5. eapply (exit_e8 (C8 cw)); try eassumption. reflexivity. }
      clear B5.
      do 5 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B6. { clear B6. eapply (exit_e8 (C8 cw)); try eassumption. reflexivity. }
      clear B6.
      do 5 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B3. { clear B3. eapply (exit_e8 (C8 cw)); try eassumption. reflexivity. }
      clear B3. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      if_cases B4. { clear B4. eapply exit_sw; exact HM'. }
      clear B4. step. (* [comment removed for export] *) step. (* [comment removed for export] *) eapply exit_sw; exact HM'.
  Qed.

  (* [comment removed for export] *)
  #[using="a1 LEN SEP1 SEP2 SEP3 RO2 RO3"] Lemma zero_digits : forall (x1 x5 x6 x7 x8 x9 x10 x11 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word)
      (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 x9 x10 x11 a2 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2b1bc) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (a1 LEN SEP1 SEP2 SEP3 RO2 RO3 : LiaFast.U) => LiaFast.u0).
    intros until r'. intros HM. pose proof HM as HM'. destruct HM as (FR' & OBJ' & DATA' & PR' & ST' & MU' & WM').
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1. eapply (exit_ec (C8 cw)); try eassumption. reflexivity.
    - clear B1. step. (* [comment removed for export] *) step. (* [comment removed for export] *) eapply exit_sw; exact HM'.
  Qed.

  #[using="LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp"] Lemma postA : forall (sd x1 x5 x6 x7 x8 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word)
      (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= bv_unsigned a1)%Z ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 x7 x8 cw x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 (Z_to_bv 64 10) x29 x30 x31)
            F (Z_to_bv 64 0x2b0d4) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp : LiaFast.U) => LiaFast.u0).
    intros until r'. intros HM H1 H2.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1. eapply zero_digits; exact HM.
    - clear B1. eapply L_digits; [exact HM | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Definition char_loop_ok (j : nat) : Prop :=
    forall (q : Z) (sd x1 x5 x6 x8 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 : word)
      (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      (Z.to_nat (bv_unsigned a1 - q) <= j)%nat ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= q)%Z -> (q < bv_unsigned a1)%Z ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 x6 (Z_to_bv 64 q) x8 cw x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 (Z_to_bv 64 10) (Z_to_bv 64 0x15db8) (Z_to_bv 64 2) (Z_to_bv 64 q))
            F (Z_to_bv 64 0x2b0ac) fc None m' (seg_rom USEGS)).

  #[using="LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp"] Lemma char_loop : forall j, char_loop_ok j.
  Proof. LiaFast.lf_pins (fun (LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp : LiaFast.U) => LiaFast.u0).
    induction j as [|j IH]; unfold char_loop_ok; intros until r'; intros HM MEAS H1 H2 H3.
    - exfalso. lia.
    - pose proof HM as HM'. destruct HM as (FR' & OBJ' & DATA' & PR' & ST' & MU' & WM').
      pose proof (bytes_at_bound _ _ _ _ DATA') as Bd.
      pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
      destruct (nth_error bs (Z.to_nat (q - bv_unsigned a0))) as [c|] eqn:Hc.
      2:{ exfalso. apply nth_error_None in Hc. lia. }
      pose proof (bv_unsigned_in_range 8 c) as Rc. unfold bv_modulus in Rc. cbn in Rc.
      pose proof (u8ro_read USEGS m' (bv_unsigned a0) bs (q - bv_unsigned a0) c _ DATA' Hc ltac:(lia) eq_refl) as RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      pose proof (table_read USEGS _ _ _ _ m' _ _ DIGTAB_ok PR' ltac:(lia) ltac:(rewrite DIGTAB_len; cbn; lia)
                    (bv_unsigned (zxb c)) ltac:(unfold zxb; rewrite unsigned_lit by lia; rewrite DIGTAB_len; lia)) as RD.
      cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in RD.
      step. (* [comment removed for export] *)
      clear RD.
      step. (* [comment removed for export] *)
      if_cases B1.
      { clear B1. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        if_cases B2.
        - clear B2. eapply L_digits; [exact HM' | lia | rewrite ?unsigned_lit by lia; lia | rewrite ?unsigned_lit by lia; lia].
        - clear B2. eapply zero_digits; exact HM'. }
      clear B1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B3.
      + cond_cleanup B3. eapply (IH (q + 1)%Z); [exact HM' | lia | lia | lia | lia].
      + cond_cleanup B3.
        replace (Z_to_bv 64 (q + 1)) with a1 by (apply bv_eq; rewrite unsigned_lit by lia; lia).
        eapply postA; [exact HM' | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp"] Lemma char_entry : forall (q : Z) (x1 x5 x8 x9 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 sd : word)
      (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= q)%Z -> (q <= bv_unsigned a1)%Z ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 (Z_to_bv 64 10) (Z_to_bv 64 q) x8 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2b090) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp : LiaFast.U) => LiaFast.u0).
    intros until r'. intros HM H1 H2 H3. pose proof HM as HM'. destruct HM as (FR' & OBJ' & DATA' & PR' & ST' & MU' & WM').
    pose proof (bytes_at_bound _ _ _ _ DATA') as Bd.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    - cond_cleanup B1.
      replace (Z_to_bv 64 q) with a1 by (apply bv_eq; rewrite unsigned_lit by lia; lia).
      eapply postA; [exact HM' | lia | lia].
    - cond_cleanup B1.
      step. step. step. step. (* [comment removed for export] *)
      eapply (char_loop _ q); [exact HM' | apply Nat.le_refl | lia | lia | lia].
  Qed.

  Ltac read_at i b Hb DATA' :=
    pose proof (u8ro_read USEGS _ (bv_unsigned a0) bs i b _ DATA' Hb ltac:(lia) eq_refl).
  Ltac have_byte i b Hb :=
    destruct (nth_error bs (Z.to_nat i)) as [b|] eqn:Hb; [ | exfalso; apply nth_error_None in Hb; lia ].

  (* [comment removed for export] *)
  #[using="LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp"] Lemma swar4_check : forall (q : Z) (sd x1 x5 x8 x9 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31 : word)
      (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= q)%Z -> (q + 4 <= bv_unsigned a1)%Z ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 (Z_to_bv 64 10) (Z_to_bv 64 q) x8 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 (Z_to_bv 64 q) x29 x30 x31)
            F (Z_to_bv 64 0x2b018) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp : LiaFast.U) => LiaFast.u0).
    intros until r'. intros HM H1 H2 H3. pose proof HM as HM'. destruct HM as (FR' & OBJ' & DATA' & PR' & ST' & MU' & WM').
    pose proof (bytes_at_bound _ _ _ _ DATA') as Bd.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    do 10 step.
    step. (* [comment removed for export] *)
    if_cases B1.
    { clear B1. eapply char_entry; [exact HM' | lia | lia | lia]. }
    clear B1.
    step. (* [comment removed for export] *) step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_not_taken.
    do 15 step.
    step. (* [comment removed for export] *)
    eapply char_entry; [exact HM' | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp"] Lemma swar4_entry : forall (q L : Z) (sd x1 x5 x8 x9 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 : word)
      (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= q)%Z -> (L = bv_unsigned a1 - q)%Z -> (0 <= L)%Z ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 (Z_to_bv 64 10) (Z_to_bv 64 q) x8 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 (Z_to_bv 64 q) (Z_to_bv 64 L) x30 x31)
            F (Z_to_bv 64 0x2afe8) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp : LiaFast.U) => LiaFast.u0).
    intros until r'. intros HM H1 H2 HL HL0. pose proof HM as HM'. destruct HM as (FR' & OBJ' & DATA' & PR' & ST' & MU' & WM').
    pose proof (bytes_at_bound _ _ _ _ DATA') as Bd.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1. eapply char_entry; [exact HM' | lia | lia | lia].
    - cond_cleanup B1.
      assert (H4 : (4 <= L)%Z).
      { assert (T : (bv_signed (Z_to_bv 64 L) <= L)%Z) by (rewrite zb_signed, unsigned_lit by lia; destruct (Z.ltb _ _); lia). lia. }
      clear B1.
      have_byte (q - bv_unsigned a0)%Z b0 Hb0. have_byte (q + 1 - bv_unsigned a0)%Z b1 Hb1.
      have_byte (q + 2 - bv_unsigned a0)%Z b2 Hb2. have_byte (q + 3 - bv_unsigned a0)%Z b3 Hb3.
      read_at (q - bv_unsigned a0)%Z b0 Hb0 DATA'. read_at (q + 1 - bv_unsigned a0)%Z b1 Hb1 DATA'.
      read_at (q + 2 - bv_unsigned a0)%Z b2 Hb2 DATA'. read_at (q + 3 - bv_unsigned a0)%Z b3 Hb3 DATA'.
      do 4 step. (* [comment removed for export] *)
      do 6 step. (* [comment removed for export] *)
      eapply swar4_check; [exact HM' | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Definition swar8_ok (j : nat) : Prop :=
    forall (q L : Z) (sd x1 x5 x10 x15 x16 x17 x24 x25 x26 x27 : word) (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      (Z.to_nat L <= j)%nat ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= q)%Z -> (L = bv_unsigned a1 - q)%Z -> (8 <= L)%Z ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 (Z_to_bv 64 10) (Z_to_bv 64 q) (Z_to_bv 64 5063812098665367110) (Z_to_bv 64 14974415777481871312)
                 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17
                 (Z_to_bv 64 9259542123273814144) (Z_to_bv 64 100000000) (Z_to_bv 64 1095216660735) (Z_to_bv 64 4294967296000100)
                 (Z_to_bv 64 42949672960001) (Z_to_bv 64 7) x24 x25 x26 x27
                 (Z_to_bv 64 q) (Z_to_bv 64 L) (Z_to_bv 64 8) (Z_to_bv 64 10))
            F (Z_to_bv 64 0x2af20) fc None m' (seg_rom USEGS)).

  #[using="LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp"] Lemma swar8_loop : forall j, swar8_ok j.
  Proof. LiaFast.lf_pins (fun (LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp : LiaFast.U) => LiaFast.u0).
    induction j as [|j IH]; unfold swar8_ok; intros until r'; intros HM MEAS H1 H2 HL H8.
    - exfalso. lia.
    - pose proof HM as HM'. destruct HM as (FR' & OBJ' & DATA' & PR' & ST' & MU' & WM').
      pose proof (bytes_at_bound _ _ _ _ DATA') as Bd.
      pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
      have_byte (q - bv_unsigned a0)%Z b0 Hb0. have_byte (q + 1 - bv_unsigned a0)%Z b1 Hb1.
      have_byte (q + 2 - bv_unsigned a0)%Z b2 Hb2. have_byte (q + 3 - bv_unsigned a0)%Z b3 Hb3.
      have_byte (q + 4 - bv_unsigned a0)%Z b4 Hb4. have_byte (q + 5 - bv_unsigned a0)%Z b5 Hb5.
      have_byte (q + 6 - bv_unsigned a0)%Z b6 Hb6. have_byte (q + 7 - bv_unsigned a0)%Z b7 Hb7.
      read_at (q - bv_unsigned a0)%Z b0 Hb0 DATA'. read_at (q + 1 - bv_unsigned a0)%Z b1 Hb1 DATA'.
      read_at (q + 2 - bv_unsigned a0)%Z b2 Hb2 DATA'. read_at (q + 3 - bv_unsigned a0)%Z b3 Hb3 DATA'.
      read_at (q + 4 - bv_unsigned a0)%Z b4 Hb4 DATA'. read_at (q + 5 - bv_unsigned a0)%Z b5 Hb5 DATA'.
      read_at (q + 6 - bv_unsigned a0)%Z b6 Hb6 DATA'. read_at (q + 7 - bv_unsigned a0)%Z b7 Hb7 DATA'.
      do 26 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B1.
      { clear B1. eapply swar4_check; [exact HM' | lia | lia | lia]. }
      clear B1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_not_taken.
      do 14 step.
      step. (* [comment removed for export] *)
      if_cases B2.
      + cond_cleanup B2.
        assert (H16 : (8 <= L + -8)%Z).
        { assert (T : (bv_signed (Z_to_bv 64 (L + -8)) <= L + -8)%Z) by (rewrite zb_signed, unsigned_lit by lia; destruct (Z.ltb _ _); lia). lia. }
        eapply (IH (q + 8)%Z (L + -8)%Z); [exact HM' | lia | lia | lia | lia | lia].
      + clear B2. step. (* [comment removed for export] *)
        eapply (swar4_entry (q + 8)%Z (L + -8)%Z); [exact HM' | lia | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  #[using="LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp"] Lemma swar4_entry_w : forall (sd x1 x5 x8 x9 x10 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x30 x31 : word)
      (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= bv_unsigned a1)%Z ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 (Z_to_bv 64 10) sd x8 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27
                 sd (Z_to_bv 64 (bv_unsigned a1 - bv_unsigned sd)) x30 x31)
            F (Z_to_bv 64 0x2afe8) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp : LiaFast.U) => LiaFast.u0).
    intros until r'. intros HM H1 H2.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    rewrite <- (Z_to_bv_bv_unsigned sd).
    eapply (swar4_entry (bv_unsigned sd)); [ | rewrite ?unsigned_lit by lia; lia ..].
    lazymatch goal with |- M2 _ _ _ => exact HM end.
  Qed.

  #[using="LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp"] Lemma swar8_w : forall (sd x1 x5 x10 x15 x16 x17 x24 x25 x26 x27 : word) (m' : word -> option byte) (cw r' : word),
      M2 m' cw r' ->
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd + 8 <= bv_unsigned a1)%Z ->
      evt USEGS POST
        (MS (mkR x1 SP' gp tp x5 (Z_to_bv 64 10) sd (Z_to_bv 64 5063812098665367110) (Z_to_bv 64 14974415777481871312)
                 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) x15 x16 x17
                 (Z_to_bv 64 9259542123273814144) (Z_to_bv 64 100000000) (Z_to_bv 64 1095216660735) (Z_to_bv 64 4294967296000100)
                 (Z_to_bv 64 42949672960001) (Z_to_bv 64 7) x24 x25 x26 x27
                 sd (Z_to_bv 64 (bv_unsigned a1 - bv_unsigned sd)) (Z_to_bv 64 8) (Z_to_bv 64 10))
            F (Z_to_bv 64 0x2af20) fc None m' (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp : LiaFast.U) => LiaFast.u0).
    intros until r'. intros HM H1 H2.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    rewrite <- (Z_to_bv_bv_unsigned sd).
    eapply (swar8_loop _ (bv_unsigned sd)); [ | apply Nat.le_refl | rewrite ?unsigned_lit by lia; lia ..].
    lazymatch goal with |- M2 _ _ _ => exact HM end.
  Qed.

  (* [comment removed for export] *)
  #[using="bs rold junk0 LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma after_zeros : forall (sd x5 x7 x9 x10 x16 x17 x28 x29 x30 x31 : word),
      (bv_unsigned a0 <= bv_unsigned sd)%Z -> (bv_unsigned sd <= bv_unsigned a1)%Z ->
      evt USEGS POST
        (MS (mkR ra SP' gp tp x5 (Z_to_bv 64 10) x7 s0 x9 x10 a1 a2 sd (Z_to_bv 64 FCI_OPT2) (Z_to_bv 64 22) x16 x17
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2aeb0) fc None m1 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold junk0 LEN NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros until x31. intros H1 H2.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    pose proof (bv_unsigned_in_range 64 sd) as Rsd. unfold bv_modulus in Rsd.
    unfold from_chars_int_W in MU.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_false.
    step. (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (HM : M2 mm x9 rold) by (split; [exact FR | split; [exact OBJ | split; [exact DATA | split; [exact PR | split; [exact ST | split; [exact MU | exact WM]]]]]]) end.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      eapply swar4_entry_w; [exact HM | lia | lia].
    - cond_cleanup B1.
      assert (H8 : (8 <= bv_unsigned a1 - bv_unsigned sd)%Z).
      { assert (T : (bv_signed (Z_to_bv 64 (bv_unsigned a1 - bv_unsigned sd)) <= bv_unsigned a1 - bv_unsigned sd)%Z)
          by (rewrite zb_signed, unsigned_lit by lia; destruct (Z.ltb _ _); lia). lia. }
      clear B1.
      do 19 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      eapply swar8_w; [exact HM | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Definition zero_ok (j : nat) : Prop :=
    forall (z : Z) (x5 x9 x10 x16 x28 x29 x30 x31 : word),
      (Z.to_nat (bv_unsigned a1 - z) <= j)%nat ->
      (bv_unsigned a0 <= z)%Z -> (z < bv_unsigned a1)%Z ->
      evt USEGS POST
        (MS (mkR ra SP' gp tp x5 (Z_to_bv 64 10) (Z_to_bv 64 (-1)) s0 x9 x10 a1 a2 (Z_to_bv 64 z) (Z_to_bv 64 FCI_OPT2) (Z_to_bv 64 22) x16 (Z_to_bv 64 48)
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x2ae98) fc None m1 (seg_rom USEGS)).

  #[using="bs rold junk0 LEN LE NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma zero_loop : forall j, zero_ok j.
  Proof. LiaFast.lf_pins (fun (bs rold junk0 LEN LE NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    induction j as [|j IH]; unfold zero_ok; intros until x31; intros MEAS H1 H2.
    - exfalso. lia.
    - pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
      have_byte (z - bv_unsigned a0)%Z c Hc.
      read_at (z - bv_unsigned a0)%Z c Hc DATA.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B1.
      { clear B1. apply after_zeros; rewrite ?unsigned_lit by lia; lia. }
      clear B1.
      step. (* [comment removed for export] *) if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B2.
      + cond_cleanup B2. eapply (IH (z + 1)%Z); lia.
      + cond_cleanup B2. step. (* [comment removed for export] *)
        apply after_zeros; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="bs rold junk0 LEN LE NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM"] Lemma body : forall (t0 t1 t2 a5 a6 a7 t3 t4 t5 t6 : word),
      evt USEGS POST
        (MS (mkR ra SP' gp tp t0 t1 t2 s0 s1 a0 a1 a2 (Z_to_bv 64 FCI_FMT) (Z_to_bv 64 FCI_OPT2) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x2adf0) fc None m1 (seg_rom USEGS)).
  Proof. LiaFast.lf_pins (fun (bs rold junk0 LEN LE NZ SEP1 SEP2 SEP3 RO2 RO3 Ra1 Rsp FR OBJ DATA PR ST MU WM : LiaFast.U) => LiaFast.u0).
    intros. unfold FCI_FMT.
    pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_true.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B0.
    { clear B0. eapply (exit_ec (CB 8 junk0)); try eassumption. reflexivity. }
    cond_cleanup B0.
    unfold FCI_OPT2.
    step. step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *) if_false.
    fold FCI_OPT2.
    step. (* [comment removed for export] *) if_not_taken.
    have_byte 0%Z c0 Hc0.
    read_at 0%Z c0 Hc0 DATA.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases B1.
    - clear B1. step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_not_taken.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases B2.
      + cond_cleanup B2. apply after_zeros; rewrite ?unsigned_lit by lia; lia.
      + cond_cleanup B2. step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
        eapply (zero_loop _ (bv_unsigned a0 + 1)%Z); try lia. apply Nat.le_refl.
    - clear B1.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_true.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) if_not_taken.
      step. (* [comment removed for export] *) step. (* [comment removed for export] *) step. (* [comment removed for export] *)
      rewrite <- (Z_to_bv_bv_unsigned a0).
      eapply (zero_loop _ (bv_unsigned a0)); try lia. apply Nat.le_refl.
  Qed.
End Proof.

Lemma from_chars_int_spec_hw : from_chars_int_stmt_hw.
Proof.
  unfold from_chars_int_stmt_hw. intros until rold. intros Ha3 Ha4 DATA NZ LEN LE OBJ ST PR SEP1 SEP2 SEP3 RO2 RO3.
  subst a3 a4.
  pose proof (munch_refl (from_chars_int_W sp a2) m) as MU.
  pose proof (wmono_refl USEGS m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Ra1. unfold bv_modulus in Ra1.
  pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
  pose proof (bytes_at_bound _ _ _ _ DATA) as Bd.
  unfold from_chars_int_W in MU.
  carve_frame 112%nat ST.
  do 14 step. (* [comment removed for export] *)
  eapply body; try eassumption; try lia.
Qed.

Lemma from_chars_int_spec : from_chars_int_stmt.
Proof. exact (from_chars_int_stmt_of_hw from_chars_int_spec_hw). Qed.
