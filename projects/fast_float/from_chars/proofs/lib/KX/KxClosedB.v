(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_stmt B_negative_digit_comp_d_stmt B_dcf_d_stmt B_dcf_f_stmt B_long_mul_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.B_small_mul_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_negative_digit_comp_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_dcf_d_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_dcf_f_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_long_mul_stmt.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_D1_closed B_dcf_d B_dcf_f B_parse_mantissa.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_6c.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_parse_mantissa_6c.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_negative_digit_comp_d B_negative_digit_comp_f B_smalloc4 B_rt_tls.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_set_shadow B_musl_memset.

Module B_asan_memset.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Perf.   (* [comment removed for export] *)
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_stmt B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_rt_lemmas.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_D1_closed.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_musl_memset_stmt.
Import OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_stmt OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_rt_m2s OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_memiszero OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_D1_closed.B_rpoison OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_musl_memset_stmt.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac lia4 ::= first [ lia_t1 | lia_t2 | lia_d1 | lia_app2 | lia_t3 ].  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation BSEGS := AsanUbsan.M.loaded_segments.

Tactic Notation "show" string(tag) := match goal with |- ?g => idtac tag g end.

(* [comment removed for export] *)
Ltac fold_snez0 :=
  replace (bv_unsigned (v_sltu (Z_to_bv 64 0) (Z_to_bv 64 0))) with 0%Z by (vm_compute; reflexivity);
  rewrite Z.land_0_l.

(* [comment removed for export] *)
Lemma big65_true : forall x, (0 <= x < 2^64)%Z ->
  negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (x + -65))) = true -> (x = 0 \/ 65 <= x)%Z.
Proof.
  intros x Hx H. apply (proj1 (Bool.negb_true_iff _)) in H. unfold bv_ltu in H. apply Z.ltb_ge in H.
  rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 64) with (2^64)%Z in H.
  Z.div_mod_to_equations. lia.
Qed.
Lemma big65_false : forall x, (0 <= x < 2^64)%Z ->
  negb (bv_ltu (Z_to_bv 64 (-65)) (Z_to_bv 64 (x + -65))) = false -> (1 <= x <= 64)%Z.
Proof.
  intros x Hx H. apply (proj1 (Bool.negb_false_iff _)) in H. unfold bv_ltu in H. apply Z.ltb_lt in H.
  rewrite !Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 64) with (2^64)%Z in H.
  Z.div_mod_to_equations. lia.
Qed.

Section Proof.
  Hypothesis RP : rpoison_stmt.
  Hypothesis MEMSET : memset_stmt.

  Section Tail.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (p vc nw : word)
              (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (c : Z) (old : list byte) (shlo shn : Z).
    Hypothesis A1 : vc = Z_to_bv 64 c.
    Hypothesis Hc8 : (0 <= c <= 255)%Z.
    Hypothesis LEN : Z.of_nat (length old) = bv_unsigned nw.
    Hypothesis ALP : (bv_unsigned p mod 8 = 0)%Z.
    Hypothesis KP1 : (app2r (bv_unsigned p) (bv_unsigned p + bv_unsigned nw + 8))%Z.
    Hypothesis KP2 : (bv_unsigned p + bv_unsigned nw + 8 <= KTOP)%Z.
    Hypothesis N40 : (bv_unsigned nw <= 2^40)%Z.
    Hypothesis RDL1 : (shlo <= ASAN_B + bv_unsigned p / 8 - (ASAN_B + bv_unsigned p / 8) mod 8)%Z.
    Hypothesis RDL2 : (ASAN_B + (bv_unsigned p + bv_unsigned nw) / 8 + 8 <= shlo + shn)%Z.
    Hypothesis SP1 : (IMG_END <= bv_unsigned sp - IMEMSET_NEED)%Z.
    Hypothesis SP2 : (KHI <= bv_unsigned sp - IMEMSET_NEED)%Z.
    Hypothesis SP3 : (bv_unsigned sp <= KTOP)%Z.
    Hypothesis SEP : (bv_unsigned sp <= bv_unsigned p \/ bv_unsigned p + bv_unsigned nw <= bv_unsigned sp - IMEMSET_NEED)%Z.
    Hypothesis RA : (bv_unsigned ra mod 2 = 0)%Z.

    Notation POST := (asan_memset_post ra sp gp tp s0 s1 p s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc c (bv_unsigned nw) m).
    Notation FRC := [C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
    Notation SP96 := (Z_to_bv 64 (bv_unsigned sp + -2128)).

    (* [comment removed for export] *)
    Definition cur (m' : word -> option byte) : Prop :=
         rw_cells BSEGS m' (bv_unsigned sp + -56) FRC
      /\ u8arr BSEGS m' (bv_unsigned p) old
      /\ stk BSEGS m' (bv_unsigned sp + -2208) (bv_unsigned sp + -56)
      /\ pristine m' RELRO_LO RELRO_HI /\ pristine m' REALTAB_LO REALTAB_HI
      /\ shz BSEGS m' (ASAN_B + bv_unsigned p / 8) ((bv_unsigned nw + 7) / 8)
      /\ rdbl BSEGS m' shlo shn
      /\ m2s_cells m'
      /\ munch (asan_memset_W sp p (bv_unsigned nw)) m m' /\ wmono BSEGS m m'.

    Ltac open_cur H := destruct H as (FR & ARR & ST & PRG & PRT & SHD & RD & M2C & MU & WM);
                       pose proof M2C as M2C'; destruct M2C' as [C1 C4]; cbv delta [asan_memset_W] in MU.
    Ltac close_cur := unfold cur; repeat match goal with |- _ /\ _ => split end; try assumption;
                      try (lazymatch goal with |- m2s_cells _ => split; assumption end).
    Ltac ranges :=
      pose proof (bv_unsigned_in_range 64 sp) as Rsp; unfold bv_modulus in Rsp;
      pose proof (bv_unsigned_in_range 64 p) as Rp; unfold bv_modulus in Rp;
      pose proof (bv_unsigned_in_range 64 nw) as Rn; unfold bv_modulus in Rn.

    (* [comment removed for export] *)
    #[using="MEMSET A1 Hc8 LEN ALP KP1 N40 SP2 SEP"] Lemma tail : forall (x1 x5 x6 x7 x8 x9 x13 x14 x15 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word) (m' : word -> option byte),
      cur m' ->
      evt BSEGS POST
        (MS (mkR x1 SP96 gp tp x5 x6 x7 x8 x9 p vc nw x13 x14 x15 x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
            F (Z_to_bv 64 0x606d4) fc None m' (seg_rom BSEGS)).
    Proof. LiaFast.lf_pins (fun (MEMSET A1 Hc8 LEN ALP KP1 N40 SP2 SEP : LiaFast.U) => LiaFast.u0).
      intros until m'. intros CUR. open_cur CUR. ranges. subst vc.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      call MEMSET.
      1:{ exact ARR. } 1:{ exact LEN. } 1:{ exact ALP. }
      step. (* [comment removed for export] *)
      do 8 step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      release_frame FR ST (bv_unsigned sp).
      unfold asan_memset_post. finish.
      match goal with
      | H : u8arr BSEGS _ _ (repeat (fillb ?cv) _) |- u8arr BSEGS _ _ _ =>
          replace (Z_to_bv 8 c) with (fillb cv); [exact H|];
          unfold fillb; rewrite unsigned_lit by lia; reflexivity
      end.
    Qed.

    (* [comment removed for export] *)
    Notation SHF := (2147450880 + bv_unsigned p / 8)%Z.
    Notation SHL := (2147450880 + (bv_unsigned p + bv_unsigned nw + -1) / 8)%Z.
    Definition qloop_ok (k : nat) : Prop :=
      forall (cu : Z) (x1 x5 x6 x7 x8 x9 x16 x17 x18 x19 x20 x21 x28 x29 x30 x31 : word) (m' : word -> option byte),
        (Z.to_nat (SHL - cu) <= k)%nat -> (SHF <= cu < SHL)%Z -> (1 <= bv_unsigned nw)%Z -> cur m' ->
        evt BSEGS POST
          (MS (mkR x1 SP96 gp tp x5 x6 x7 x8 x9 p vc nw (Z_to_bv 64 cu) (Z_to_bv 64 SHL) (Z_to_bv 64 0) x16 x17 x18 x19 x20 x21 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x60800) fc None m' (seg_rom BSEGS)).
    #[using="MEMSET A1 Hc8 LEN ALP KP1 N40 SP2 SP3 SEP"] Lemma qloop : forall k, qloop_ok k.
    Proof. LiaFast.lf_pins (fun (MEMSET A1 Hc8 LEN ALP KP1 N40 SP2 SP3 SEP : LiaFast.U) => LiaFast.u0).
      induction k as [|k IH]; unfold qloop_ok; intros until m'; intros Hk Hc Hn CUR; [lia|].
      pose proof CUR as CUR'. open_cur CUR'. ranges. pose proof (shz_bound _ _ _ _ SHD) as Bsh.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hb.
      - cond_cleanup Hb. eapply (IH (cu + 1)%Z); try eassumption; lia.
      - cond_cleanup Hb.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        eapply tail; eassumption.
    Qed.
  End Tail.

  Ltac prove_cur :=
    try (progress unfold cur; repeat match goal with |- _ /\ _ => split end;
         first [ eassumption | split; eassumption | idtac ]).

  #[using="RP MEMSET"] Lemma asan_memset_spec : asan_memset_stmt.
  Proof. LiaFast.lf_pins (fun (RP MEMSET : LiaFast.U) => LiaFast.u0).
    unfold asan_memset_stmt. intros until shn.
    intros A1 Hc8 ARR LEN ALP KP1 KP2 N40 SHD RD RDL1 RDL2 ST SP1 SP2 SP3 AL16 SEP PRG PRT RTH RDJ1 RDJ2 RA.
    pose proof (munch_refl (asan_memset_W sp a0 (bv_unsigned a2)) m) as MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a0) as Ra0. unfold bv_modulus in Ra0.
    pose proof (bv_unsigned_in_range 64 a2) as Ra2. unfold bv_modulus in Ra2.
    pose proof (shz_bound _ _ _ _ SHD) as Bsh.
    pose proof RD as RD'. destruct RD' as (Brd1 & Brd2 & _).
    open_RT_keep RTH.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Hc1 & Hc2 & Ht1 & Ht2 & Hb1 & Hb2).
    clear RT2 RT2b RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb RTH.
    cbv delta [asan_memset_W] in MU.
    carve_frame 56%nat ST.
    do 8 step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. step. (* [comment removed for export] *)
    match goal with H : stk _ _ ?lo (bv_unsigned sp + -56) |- _ => replace lo with (bv_unsigned sp + -2208)%Z in H by lia end.
    step. (* [comment removed for export] *)
    if_cases Hov. { exfalso. cond_cleanup Hov. rewrite ?zb_lxor_ones in Hov by lia. lia. } clear Hov.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hbig.
    - (* [comment removed for export] *)
      apply big65_true in Hbig; [ | lia ].
      step. (* [comment removed for export] *)
      if_cases Hz.
      + cond_cleanup Hz.
        step. step. step. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        match goal with H : stk _ ?mc ?lo (bv_unsigned sp + -56) |- _ =>
          destruct (stk_split BSEGS mc _ (bv_unsigned sp + -2128) _ H ltac:(lia)) as [STlo SThi]; clear H end.
        pose proof (unsigned_lit (bv_unsigned sp + -2128) ltac:(lia)) as Usp.
        call RP.
        1:{ rewrite ?unsigned_lit by lia. Z.div_mod_to_equations. lia. }
        1:{ rewrite ?unsigned_lit by lia. lia. }
        1:{ eapply shz_sub; [exact SHD | lia | Z.div_mod_to_equations; lia | Z.div_mod_to_equations; lia]. }
        1:{ split; assumption. } 1:{ exact PRG. }
        1:{ rewrite Usp. replace (bv_unsigned sp + -2128 - RP_NEED)%Z with (bv_unsigned sp + -2208)%Z by lia. exact STlo. }
        1:{ rewrite Usp. lia. } 1:{ rewrite Usp. lia. }
        1:{ rewrite unsigned_lit by lia. reflexivity. }
        clear Usp.
        step. step. step. step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        match goal with H1 : stk _ ?mc ?lo (bv_unsigned sp + -2128), H2 : stk _ ?mc (bv_unsigned sp + -2128) _ |- _ =>
          pose proof (stk_merge BSEGS mc _ _ _ H1 H2 ltac:(lia)) as ST'; clear H1 H2;
          replace lo with (bv_unsigned sp + -2208)%Z in ST' by lia end.
        eapply tail; try eassumption. prove_cur.
      + (* [comment removed for export] *)
        cond_cleanup Hz.
        step. (* [comment removed for export] *)
        eapply tail; try eassumption. prove_cur.
    - (* [comment removed for export] *)
      apply big65_false in Hbig; [ | lia ]. rename Hbig into Hn.
      step. step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2147450880 + bv_unsigned a0 / 8)) by lia.
      rewrite (land_m8w (2147450880 + bv_unsigned a0 / 8)) by lia.
      step. (* [comment removed for export] *)
      rewrite (unsigned_lit (2147450880 + (bv_unsigned a0 + bv_unsigned a2 + -1) / 8)) by (Z.div_mod_to_equations; lia).
      rewrite (land_m8w (2147450880 + (bv_unsigned a0 + bv_unsigned a2 + -1) / 8)) by (Z.div_mod_to_equations; lia).
      set (SHF := (2147450880 + bv_unsigned a0 / 8)%Z) in *.
      set (SHL := (2147450880 + (bv_unsigned a0 + bv_unsigned a2 + -1) / 8)%Z) in *.
      assert (Hsh : (ASAN_B <= SHF <= SHL /\ SHL <= KHI /\ SHL - SHF + 1 <= (bv_unsigned a2 + 7) / 8)%Z) by (subst SHF SHL; Z.div_mod_to_equations; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        destruct (rdbl_read BSEGS mc shlo shn (SHF - SHF mod 8)%Z 8 RD ltac:(subst SHF; Z.div_mod_to_equations; lia) ltac:(subst SHF SHL; Z.div_mod_to_equations; lia)) as (w1 & Lw1 & R1) end.
      step. (* [comment removed for export] *)
      clear R1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        destruct (rdbl_read BSEGS mc shlo shn (SHL - SHL mod 8)%Z 8 RD ltac:(subst SHF SHL; Z.div_mod_to_equations; lia) ltac:(subst SHL; Z.div_mod_to_equations; lia)) as (w2 & Lw2 & R2) end.
      step. (* [comment removed for export] *)
      clear R2.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      if_cases Hq.
      + clear Hq.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        fold_snez0.
        step. (* [comment removed for export] *)
        if_cases Hge.
        * cond_cleanup Hge.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          eapply tail; try eassumption. prove_cur.
        * cond_cleanup Hge.
          eapply qloop with (c := c) (old := old) (shlo := shlo) (shn := shn) (m := m)
                            (k := Z.to_nat (SHL - SHF)) (cu := SHF); try eassumption; try lia.
          prove_cur.
      + clear Hq. eapply tail; try eassumption. prove_cur.
  Qed.
End Proof.
End B_asan_memset.

From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require KxLMnB.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require B_compare.
From OSSVerify.Proofs.fast_float.from_chars.lib.KX Require KxLMeB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition B_long_mul_closed : long_mul_stmt := KxLMeB.long_mul_fx.
Definition B_set_shadow_f5_closed : set_shadow_f5_stmt := B_set_shadow.set_shadow_f5_spec B_musl_memset.memset_spec.
Definition B_smalloc4_closed : smalloc4_stmt := B_smalloc4.smalloc4_spec B_rt_tls.tls_chain_spec OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_rt_lemmas.B_rt_m2s.m2s_spec.
Definition B_asan_memset_closed : asan_memset_stmt :=
  B_asan_memset.asan_memset_spec B_D1_closed.B_rpoison_closed B_musl_memset.memset_spec.
Definition B_parse_mantissa_closed : parse_mantissa_stmt :=
  B_parse_mantissa.parse_mantissa_spec OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_small_mul.small_mul_spec OSSVerify.Proofs.fast_float.from_chars.lib.FFB.B_parse_mantissa_6c.B_small_add.small_add_spec.
Definition B_pos_dc_d_closed := B_D1_closed.B_pos_dc_d_closed B_long_mul_closed.
Definition B_pos_dc_f_closed := B_D1_closed.B_pos_dc_f_closed B_long_mul_closed.
Definition B_neg_dc_d_closed :=
  B_negative_digit_comp_d.negative_digit_comp_d_spec B_smalloc4_closed B_asan_memset_closed OSSVerify.Proofs.fast_float.from_chars.lib.KX.KxLMnB.B_normalize.normalize_spec
    (B_D1_closed.B_pow5_closed B_long_mul_closed) B_D1_closed.B_shl_closed B_compare.compare_spec B_set_shadow_f5_closed.
Definition B_neg_dc_f_closed :=
  B_negative_digit_comp_f.negative_digit_comp_f_spec B_smalloc4_closed B_asan_memset_closed OSSVerify.Proofs.fast_float.from_chars.lib.KX.KxLMnB.B_normalize.normalize_spec
    (B_D1_closed.B_pow5_closed B_long_mul_closed) B_D1_closed.B_shl_closed B_compare.compare_spec B_set_shadow_f5_closed.
Definition B_dcf_d_closed : dcf_d_stmt :=
  B_dcf_d.dcf_d_spec B_asan_memset_closed B_parse_mantissa_closed B_pos_dc_d_closed B_neg_dc_d_closed.
Definition B_dcf_f_closed : dcf_f_stmt :=
  B_dcf_f.dcf_f_spec B_asan_memset_closed B_parse_mantissa_closed B_pos_dc_f_closed B_neg_dc_f_closed.
