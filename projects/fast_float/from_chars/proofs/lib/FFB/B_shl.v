(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common.Lib Require Import Tac.
From OSSVerify.Proofs.fast_float.from_chars.lib.LibAsan Require Import Shadow.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFB Require Import B_rt_stmt B_rt_lemmas B_shl_bits_stmt B_shl_limbs_stmt B_shl_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
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

Lemma stk_subS : forall m lo hi lo' hi',
  stk BSEGS m lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> (lo' <= hi')%Z -> stk BSEGS m lo' hi'.
Proof.
  intros m lo hi lo' hi' ST H1 H2 H3.
  destruct (stk_split BSEGS m lo lo' hi ST ltac:(lia)) as [_ ST1].
  destruct (stk_split BSEGS m lo' hi' hi ST1 ltac:(lia)) as [ST2 _]. exact ST2.
Qed.

Section Main.
  Hypothesis shl_bits_spec : shl_bits_stmt.
  Hypothesis shl_limbs_spec : shl_limbs_stmt.

  Section Fixed.
  Variables (ra sp gp tp a0 a1 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (ws : list word) (len : Z) (j5 : list byte) (v : rt_vals).
  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a1).
  Notation POST := (shl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n ws len m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -32)).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis A0p : (0 < A)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 2384 \/ bv_unsigned sp <= A)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis SPB : (0 <= bv_unsigned sp - 2384)%Z.
  Hypothesis HA : (0 <= A /\ A + 498 <= 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis PRG : pristine m RELRO_LO RELRO_HI.
  Hypothesis PRT : pristine m REALTAB_LO REALTAB_HI.
  Hypothesis RTH0 : RT m v.
  Hypothesis RD1 : rt_disj v (bv_unsigned sp - 2384) (bv_unsigned sp).
  Hypothesis RD2 : rt_disj v A (A + 498).
  Hypothesis SPLO : (IMG_END <= bv_unsigned sp - 2384)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp - 2384)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (A) (A + 504))%Z.
  Hypothesis KA1 : (A + 504 <= KTOP)%Z.
  Hypotheses (Kc1 : rt_app (rt_ctx v) 160) (Kc2 : (rt_ctx v + 160 <= KTOP)%Z) (Kt1 : rt_app (rt_thr v) 80)
             (Kt2 : (rt_thr v + 80 <= KTOP)%Z) (Kb1 : rt_app (rt_blk v) 32) (Kb2 : (rt_blk v + 32 <= KTOP)%Z).

  Ltac solve_W := solve_W_rt.  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="shl_limbs_spec v L62 Hlen A8 A0p SEP Rsp SPB AL RTH0 RD1 RD2 SPLO KSP KSP2 KA0 Kc1 Kt1 Kb1"] Lemma shl_from_80 : forall (x1 t0 t1 t2 x10 x11 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m1 : word -> option byte) (ws1 : list word) (len1 : Z),
    u64arr BSEGS m1 A ws1 -> length ws1 = 62%nat ->
    rw_cells BSEGS m1 (A + 496) [C2 (Z_to_bv 64 len1)] -> (0 <= len1 <= 62)%Z ->
    stk BSEGS m1 (bv_unsigned sp - 2384) (bv_unsigned sp + -32) ->
    rw_cells BSEGS m1 (bv_unsigned sp + -32) [CB 8 j5; C8 s1; C8 s0; C8 ra] ->
    munch (shl_W (bv_unsigned sp) A) m m1 -> wmono BSEGS m m1 ->
    pristine m1 RELRO_LO RELRO_HI -> pristine m1 REALTAB_LO REALTAB_HI ->
    shz BSEGS m1 (ASAN_B + A / 8) 63 -> rdbl BSEGS m1 (ASAN_B + A / 8 - 8) 79 ->
    bval ws1 (Z.to_nat len1) = (bval ws (Z.to_nat len) * 2 ^ (n mod 64))%Z ->
    (bnorm ws (Z.to_nat len) -> bnorm ws1 (Z.to_nat len1)) ->
    (len1 <= len + 1)%Z -> ((0 < len)%Z -> (0 < len1)%Z) ->
    evt BSEGS POST (MS (mkR x1 SP' gp tp t0 t1 t2 a1 a0 x10 x11 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                       F (Z_to_bv 64 0x985ac) fc None m1 (seg_rom BSEGS)).
  Proof. LiaFast.lf_pins (fun (shl_limbs_spec v L62 Hlen A8 A0p SEP Rsp SPB AL RTH0 RD1 RD2 SPLO KSP KSP2 KA0 Kc1 Kt1 Kb1 : LiaFast.U) => LiaFast.u0).
    intros * CUR L1 LENC Hlen1 ST FR MU WM PRG1 PRT1 SHX1 RBX1 VAL BN LB LP.
    cbv delta [shl_W] in MU.
    pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn.
    pose proof (bval_nonneg ws (Z.to_nat len)) as X0.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H64.
    - cond_cleanup H64.
      step. (* [comment removed for export] *)
      do 5 step.
      release_frame FR ST (bv_unsigned sp).
      unfold shl_post. finish.
      { exact CUR. } { exact L1. } { exact LENC. } all: try lia.
      intros BN0 CAP _. split; [reflexivity|]. split; [| apply BN; exact BN0].
      rewrite VAL. rewrite Z.mod_small by lia. reflexivity.
    - cond_cleanup H64.
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6)%Z with 64%Z.
      step. (* [comment removed for export] *)
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
      pose proof (unsigned_lit (n / 64) ltac:(split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia])) as ULd.
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [ eapply shl_limbs_spec with (ws := ws1) (len := len1) (v := v) | post_call BSEGS mc ] end.
      all: try lazymatch goal with
           | |- evt _ _ _ => idtac
           | |- u64arr _ _ _ _ => exact CUR
           | |- rw_cells _ _ _ [C2 _] => exact LENC
           | |- pristine _ RELRO_LO _ => exact PRG1
           | |- pristine _ _ _ => exact PRT1
           | |- shz _ _ _ _ => exact SHX1
           | |- rdbl _ _ _ _ => exact RBX1
           | |- RT _ _ => eapply RT_transport; [exact RTH0 | exact MU | solve_W]
           | |- rt_disj _ _ _ => rewrite ?ULs; first [exact RD2 | eapply rt_disj_sub; [exact RD1 | lia | lia]]
           | |- stk _ _ _ _ => rewrite ULs; replace (bv_unsigned sp + -32 - 2352)%Z with (bv_unsigned sp - 2384)%Z by lia; exact ST
           | |- (bv_unsigned _ < 2 ^ 58)%Z => rewrite ULd; apply Z.div_lt_upper_bound; lia
           | |- _ => rewrite ?ULs, ?ULd; first [eassumption | reflexivity | lia | (Z.div_mod_to_equations; lia)]
           end.
      all: match goal with |- evt _ _ _ => idtac | |- ?g => idtac "REMAIN-SL" g end.
      rewrite ?ULs, ?ULd in *.
      match goal with H : (0 <= ?x <= 1)%Z |- _ => rename x into b end.
      step. (* [comment removed for export] *)
      if_cases Hb.
      + (* [comment removed for export] *)
        cond_cleanup Hb.
        do 5 step.
        match goal with H : stk BSEGS _ _ _ |- _ => rename H into ST' end.
        replace (bv_unsigned sp + -32 - 2352)%Z with (bv_unsigned sp - 2384)%Z in ST' by lia.
        release_frame FR ST' (bv_unsigned sp).
        unfold shl_post. finish. all: try eassumption. all: try lia.
        intros BN0 CAP SMALL. exfalso.
        rewrite ?unsigned_lit in Hb by lia.
        match goal with H : (_ <= 62)%Z -> b = 1%Z |- _ => enough (n / 64 + len1 <= 62)%Z by lia end.
        (* [comment removed for export] *)
        destruct (Z.eq_dec len 0) as [L0|L0].
        * (* [comment removed for export] *)
          destruct SMALL as [|SMALL]; [lia|].
          assert (n / 64 < 63)%Z by (apply Z.div_lt_upper_bound; lia).
          destruct (Z.eq_dec len1 0) as [|L1nz]; [lia|]. exfalso.
          pose proof (bnorm_lower ws1 (Z.to_nat len1) (BN BN0) ltac:(lia)) as LO.
          rewrite VAL, L0 in LO. change (Z.to_nat 0) with 0%nat in LO. rewrite bval_0, Z.mul_0_l in LO.
          pose proof (pow64_pos (Z.to_nat len1 - 1)). lia.
        * pose proof (BN BN0) as BN1. specialize (LP ltac:(lia)).
          pose proof (bnorm_lower ws1 (Z.to_nat len1) BN1 ltac:(lia)) as LO.
          unfold BIG_CAP in CAP. rewrite (pow2_split64 n) in CAP by lia.
          rewrite VAL in LO.
          assert (E1 : (2 ^ (64 * Z.of_nat (Z.to_nat len1 - 1)) * 2 ^ (64 * (n / 64)) < 2 ^ 3968)%Z).
          { eapply Z.le_lt_trans; [| exact CAP].
            replace (bval ws (Z.to_nat len) * (2 ^ (n mod 64) * 2 ^ (64 * (n / 64))))%Z
               with (bval ws (Z.to_nat len) * 2 ^ (n mod 64) * 2 ^ (64 * (n / 64)))%Z by ring.
            apply Z.mul_le_mono_nonneg_r; [apply Z.pow_nonneg; lia| exact LO]. }
          rewrite <- Z.pow_add_r in E1 by lia. apply Z.pow_lt_mono_r_iff in E1; lia.
      + cond_cleanup Hb. rewrite ?unsigned_lit in Hb by lia.
        match goal with H : b = 1%Z -> _ |- _ => destruct (H ltac:(lia)) as [VAL2 BN2] end.
        step. (* [comment removed for export] *)
        do 5 step.
        match goal with H : stk BSEGS _ _ _ |- _ => rename H into ST' end.
        replace (bv_unsigned sp + -32 - 2352)%Z with (bv_unsigned sp - 2384)%Z in ST' by lia.
        release_frame FR ST' (bv_unsigned sp).
        unfold shl_post. finish. all: try eassumption. all: try lia.
        intros BN0 CAP _. split; [reflexivity|]. split.
        * rewrite VAL2, VAL. rewrite <- Z.mul_assoc, <- Z.pow_add_r by (try apply Z.mul_nonneg_nonneg; try apply Z.div_pos; try apply Z.mod_pos_bound; lia).
          f_equal. f_equal. pose proof (Z.div_mod n 64 ltac:(lia)). lia.
        * apply BN2. apply BN. exact BN0.
  Qed.
  End Fixed.

  #[using="shl_bits_spec shl_limbs_spec"] Lemma shl_spec : shl_stmt.
  Proof. LiaFast.lf_pins (fun (shl_bits_spec shl_limbs_spec : LiaFast.U) => LiaFast.u0).
    unfold shl_stmt. intros until v. intros ST AL LIMBS L62 LENC Hlen A8 SEP PRG PRT RTH RD1 RD2 SPLO KSP KSP2 KA0 KA1 SHX RBX.
    assert (A0p : (0 < bv_unsigned a0)%Z) by lia.
    pose proof RTH as RTH0. open_RT_keep RTH.
    destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Kc1 & Kc2 & Kt1 & Kt2 & Kb1 & Kb2).
    assert (BC : ro_cells BSEGS m 943736 [C8 (Z_to_bv 64 ASAN_B)]).
    { change [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)] with ([C8 (Z_to_bv 64 ASAN_B)] ++ [C4 (Z_to_bv 64 1)]) in RT1.
      apply (proj1 (proj1 (ro_cells_app BSEGS m 943736 _ _) RT1)). }
    clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb RTH.
    pose proof (munch_refl (shl_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
    cbv delta [shl_W] in MU.
    pose proof (wmono_refl BSEGS m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
    pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn.
    pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    assert (HA : (0 <= bv_unsigned a0 /\ bv_unsigned a0 + 498 <= 2 ^ 64)%Z) by lia. clear Bl Bc.
    assert (SPB : (0 <= bv_unsigned sp - 2384)%Z) by (destruct ST as (? & ? & ?); lia).
    carve_frame 32%nat ST.
    do 4 step. (* [comment removed for export] *)
    match type of FR with context [CB 8 ?j] => remember j as j5 eqn:E5 in FR; clear E5 end.
    step. (* [comment removed for export] *)
    zstep. (* [comment removed for export] *)
    change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6)%Z with 64%Z.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases Hrem.
    - cond_cleanup Hrem.
      eapply shl_from_80; try eassumption; try lia.
      all: first [ rewrite Hrem, Z.pow_0_r; lia | intros B; exact B | idtac ].
      all: match goal with |- ?g => idtac "REMAIN-M0" g end.
    - cond_cleanup Hrem.
      step. (* [comment removed for export] *)
      pose proof (unsigned_lit (bv_unsigned sp + -32) ltac:(lia)) as ULs.
      step. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
        eapply evt_cut; [ eapply shl_bits_spec with (ws := ws) (len := len) | post_call BSEGS mc ] end.
      all: try lazymatch goal with
           | |- evt _ _ _ => idtac
           | |- u64arr _ _ _ _ => exact LIMBS
           | |- rw_cells _ _ _ [C2 _] => exact LENC
           | |- pristine _ _ _ => exact PRG
           | |- ro_cells _ _ _ _ => exact BC
           | |- shz _ _ _ _ => exact SHX
           | |- stk _ _ _ _ => rewrite ULs; eapply stk_subS; [exact ST | lia | lia | lia]
           | |- (1 <= _ <= 63)%Z => rewrite unsigned_lit by lia; pose proof (Z.mod_pos_bound (bv_unsigned a1) 64 ltac:(lia)); lia
           | |- _ => rewrite ?ULs; first [eassumption | reflexivity | lia]
           end.
      all: match goal with |- evt _ _ _ => idtac | |- ?g => idtac "REMAIN-SB" g end.
      rewrite ?ULs in *.
      match goal with H : (0 <= ?x <= 1)%Z |- _ => rename x into b end.
      step. (* [comment removed for export] *)
      if_cases Hb.
      + cond_cleanup Hb.
        do 5 step.
        release_frame FR ST (bv_unsigned sp).
        unfold shl_post. finish. all: try eassumption. all: try lia.
        intros BN0 CAP _. exfalso.
        rewrite unsigned_lit in * by lia.
        match goal with H : (_ < BIG_CAP)%Z -> b = 1%Z |- _ => enough (b = 1%Z) by lia; apply H end.
        eapply Z.le_lt_trans; [| exact CAP]. apply Z.mul_le_mono_nonneg_l; [apply bval_nonneg|].
        apply Z.pow_le_mono_r; [lia|]. apply Z.mod_le; lia.
      + cond_cleanup Hb.
        rewrite unsigned_lit in * by lia.
        match goal with H : b = 1%Z -> _ |- _ => destruct (H ltac:(lia)) as (VAL1 & LB1 & BN1) end.
        try match goal with H : stk BSEGS _ (bv_unsigned sp + -32 - 16) _ |- _ => clear H end.
        eapply shl_from_80; try eassumption; try lia.
        all: match goal with |- ?g => idtac "REMAIN-M" g end.
  Qed.
End Main.
