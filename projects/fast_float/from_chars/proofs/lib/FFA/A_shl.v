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
From OSSVerify.fast_float.from_chars.images Require Import Asan.
From OSSVerify.Proofs.fast_float.from_chars.lib.FF Require Import Bigint_defs Bigint_shl.
From OSSVerify.Proofs.fast_float.from_chars.lib.FFA Require Import A_rt_stmt A_rt_lemmas A_shl_bits_stmt A_shl_stmt.
Local Ltac lia ::= lia_tc.  (* [comment removed for export] *)
Local Ltac step ::=
  app2_lin_all;
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step_core segs R F pc fc rv m ro; try decide_lit_if
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.  (* [comment removed for export] *)
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac simpl_arr_sizes ::= tryif kp_sas_pre5 then (rewrite ?u32s_length, ?u64s_length, ?upd_length, ?zeros_length, ?repeat_length in *) else idtac.      (* [comment removed for export] *)

Ltac name_mem X := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into X end.
Ltac solve_W_ok_rt := solve_W_rt.  (* [comment removed for export] *)

Lemma stk_sub : forall m lo hi lo' hi',
  stk ASEGS m lo hi -> (lo <= lo')%Z -> (hi' <= hi)%Z -> (lo' <= hi')%Z -> stk ASEGS m lo' hi'.
Proof.
  intros m lo hi lo' hi' ST H1 H2 H3.
  destruct (stk_split ASEGS m lo lo' hi ST ltac:(lia)) as [_ ST1].
  destruct (stk_split ASEGS m lo' hi' hi ST1 ltac:(lia)) as [ST2 _]. exact ST2.
Qed.

(* [comment removed for export] *)
Ltac ulit := repeat (rewrite unsigned_lit by lia).
Ltac zlia := ulit; first [lia | Z.div_mod_to_equations; lia].
Ltac side :=
  lazymatch goal with
  | |- evt _ _ _ => idtac
  | |- RT _ _ => eapply RT_transport; [eassumption | eassumption | solve_W_ok_rt]
  | |- rt_disj _ _ _ => ulit; match goal with H : rt_disj _ _ _ |- _ => eapply rt_disj_sub; [exact H | lia | lia] end
  | |- shz _ _ _ _ => ulit; first [eassumption | match goal with H : shz _ _ _ _ |- _ => eapply shz_sub; [exact H | zlia | zlia | zlia] end]
  | |- stk _ _ _ _ => ulit; first [eassumption | match goal with H : stk _ _ _ _ |- _ => eapply stk_sub; [exact H | lia | lia | lia] end]
  | |- @eq word _ _ => first [reflexivity | ulit; reflexivity]
  | |- _ => first [eassumption | reflexivity | zlia]
  end.

Section Main.
  Hypothesis shl_bits_spec : shl_bits_stmt.
  Hypothesis asan_memmove_spec : asan_memmove_stmt.
  Hypothesis asan_memset_spec : asan_memset_stmt.

Section From.
  Variables (ra sp gp tp s0 s1 a0 a1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
            (ws : list word) (len : Z) (v : rt_vals).
  Notation A := (bv_unsigned a0).
  Notation n := (bv_unsigned a1).
  Notation POST := (shl_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A n ws len m).
  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -48)).
  Notation BB := (Z_to_bv 64 ASAN_B).
  Hypothesis L62 : length ws = 62%nat.
  Hypothesis Hlen : (0 <= len <= 62)%Z.
  Hypothesis A8 : (A mod 8 = 0)%Z.
  Hypothesis AL : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis SEP : (A + 498 <= bv_unsigned sp - 2272 \/ bv_unsigned sp <= A)%Z.
  Hypothesis Rsp : (0 <= bv_unsigned sp < 2 ^ 64)%Z.
  Hypothesis Bl : (0 <= A /\ A + 8 * Z.of_nat 62 <= 2 ^ 64)%Z.
  Hypothesis RTH : RT m v.
  Hypothesis RD1 : rt_disj v (bv_unsigned sp - 2272) (bv_unsigned sp).
  Hypothesis RD2 : rt_disj v A (A + 498).
  Hypothesis SPLO : (IMG_END <= bv_unsigned sp - 2272)%Z.
  Hypothesis KSP : (KHI <= bv_unsigned sp - 2272)%Z.
  Hypothesis KSP2 : (bv_unsigned sp <= KTOP)%Z.
  Hypothesis KA0 : (app2r (A) (A + 504))%Z.
  Hypothesis KA1 : (A + 504 <= KTOP)%Z.
  Hypotheses (Hc1 : rt_app (rt_ctx v) 160) (Hc2 : (rt_ctx v + 160 <= KTOP)%Z) (Ht1 : rt_app (rt_thr v) 80)
             (Ht2 : (rt_thr v + 80 <= KTOP)%Z) (Hb1 : rt_app (rt_blk v) 32) (Hb2 : (rt_blk v + 32 <= KTOP)%Z).

  (* [comment removed for export] *)
  #[using="asan_memmove_spec asan_memset_spec v L62 Hlen A8 AL SEP Rsp Bl RTH RD1 RD2 SPLO KSP KSP2 KA0 KA1 Hc1 Ht1 Hb1"] Lemma shl_from : forall (x1 x5 x6 x7 x10 x11 a2 a3 a4 a5 a6 a7 x28 x29 x30 x31 : word)
                          (m1 : word -> option byte) (ws1 : list word) (len1 : Z),
    u64arr ASEGS m1 A ws1 -> length ws1 = 62%nat ->
    rw_cells ASEGS m1 (A + 496) [C2 (Z_to_bv 64 len1)] -> (0 <= len1 <= 62)%Z ->
    stk ASEGS m1 (bv_unsigned sp - 2272) (bv_unsigned sp + -48) ->
    rw_cells ASEGS m1 (bv_unsigned sp + -48) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    munch (shl_W (bv_unsigned sp) A) m m1 -> wmono ASEGS m m1 ->
    pristine m1 RELRO_LO RELRO_HI -> pristine m1 REALTAB_LO REALTAB_HI ->
    shz ASEGS m1 (ASAN_B + A / 8) 63 -> rdbl ASEGS m1 (ASAN_B + A / 8 - 8) 79 ->
    bval ws1 (Z.to_nat len1) = (bval ws (Z.to_nat len) * 2 ^ (n mod 64))%Z ->
    (bnorm ws (Z.to_nat len) -> bnorm ws1 (Z.to_nat len1)) ->
    evt ASEGS POST (MS (mkR x1 SP' gp tp x5 x6 x7 s0 a0 x10 x11 a2 a3 a4 a5 a6 a7 a1 BB s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x979e4) fc None m1 (seg_rom ASEGS)).
  Proof. LiaFast.lf_pins (fun (asan_memmove_spec asan_memset_spec v L62 Hlen A8 AL SEP Rsp Bl RTH RD1 RD2 SPLO KSP KSP2 KA0 KA1 Hc1 Ht1 Hb1 : LiaFast.U) => LiaFast.u0).
    intros x1 x5 x6 x7 x10 x11 a2 a3 a4 a5 a6 a7 x28 x29 x30 x31 m1 ws1 len1 CUR L1 LENC Hlen1 ST FR MU WM PRG PRT SHX RBX VAL BN.
    cbv delta [shl_W] in MU.
    pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn.
    pose proof (rw_cells_bound _ _ _ _ LENC) as Bc. cbn [cells_size csize Nat.add] in Bc.
    step. (* [comment removed for export] *)
    step. (* [comment removed for export] *)
    if_cases H64.
    - (* [comment removed for export] *)
      cond_cleanup H64.
      step. (* [comment removed for export] *)
      do 8 step.
      release_frame FR ST (bv_unsigned sp).
      unfold shl_post. finish.
      { exact CUR. } { exact L1. } { exact LENC. } all: try lia.
      intros BN0 CAP _. split; [reflexivity|]. split; [| apply BN; exact BN0].
      rewrite VAL. rewrite Z.mod_small by lia. reflexivity.
    - cond_cleanup H64.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *) shr3.
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      step. (* [comment removed for export] *)
      rewrite zx16_lit_small by lia.
      zstep. (* [comment removed for export] *)
      rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 6)%Z with 64%Z.
      zstep. (* [comment removed for export] *)
      remember (n / 64)%Z as d eqn:Dd.
      assert (Hd : (1 <= d < 2 ^ 58)%Z). { subst d. split. { apply Z.div_le_lower_bound; lia. } apply Z.div_lt_upper_bound; lia. }
      step. (* [comment removed for export] *)
      if_cases Hz.
      + cond_cleanup Hz. subst len1.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hov.
        * cond_cleanup Hov.
          step. step. (* [comment removed for export] *)
          do 8 step.
          release_frame FR ST (bv_unsigned sp).
          unfold shl_post. finish.
          { exact CUR. } { exact L1. } { exact LENC. } all: try lia.
          intros BN0 CAP SMALL. exfalso.
          change (Z.to_nat 0) with 0%nat in VAL. rewrite bval_0 in VAL.
          assert (Hp : (0 < 2 ^ (n mod 64))%Z) by (apply Z.pow_pos_nonneg; [lia| apply Z.mod_pos_bound; lia]).
          assert (B0 : bval ws (Z.to_nat len) = 0%Z) by nia.
          destruct BN0 as [BN0|BN0].
          -- assert (len = 0)%Z by lia. destruct SMALL as [|SMALL]; [lia|].
             assert (n / 64 < 63)%Z by (apply Z.div_lt_upper_bound; lia). lia.
          -- pose proof (bnorm_lower ws (Z.to_nat len) (or_intror BN0) ltac:(lia)) as LO.
             pose proof (pow64_pos (Z.to_nat len - 1)). lia.
        * cond_cleanup Hov.
          step. (* [comment removed for export] *)
          do 8 step.
          release_frame FR ST (bv_unsigned sp).
          unfold shl_post. finish.
          { exact CUR. } { exact L1. } { exact LENC. } all: try lia.
          intros BN0 CAP _. change (Z.to_nat 0) with 0%nat in VAL |- *. rewrite bval_0 in VAL |- *.
          assert (Hp : (0 < 2 ^ (n mod 64))%Z) by (apply Z.pow_pos_nonneg; [lia| apply Z.mod_pos_bound; lia]).
          assert (B0 : bval ws (Z.to_nat len) = 0%Z) by nia.
          split; [reflexivity|]. split; [rewrite B0; lia| apply bnorm_0].
      + cond_cleanup Hz.
        step. (* [comment removed for export] *)
        step. (* [comment removed for export] *)
        if_cases Hov.
        * cond_cleanup Hov.
          step. step. (* [comment removed for export] *)
          if_taken.
          step. step. (* [comment removed for export] *)
          do 8 step.
          release_frame FR ST (bv_unsigned sp).
          unfold shl_post. finish.
          { exact CUR. } { exact L1. } { exact LENC. } all: try lia.
          intros BN0 CAP SMALL. exfalso.
          pose proof (BN BN0) as BN1.
          pose proof (bnorm_lower ws1 (Z.to_nat len1) BN1 ltac:(lia)) as LO.
          unfold BIG_CAP in CAP.
          rewrite (pow2_split64 n) in CAP by lia. rewrite <- Dd in CAP.
          assert (E1 : (2 ^ (64 * 62) <= 2 ^ (64 * Z.of_nat (Z.to_nat len1 - 1)) * 2 ^ (64 * d))%Z).
          { rewrite <- Z.pow_add_r by lia. apply Z.pow_le_mono_r; lia. }
          pose proof (pow64_pos (Z.to_nat len1 - 1)). assert (0 < 2 ^ (64 * d))%Z by (apply Z.pow_pos_nonneg; lia).
          pose proof (bval_nonneg ws (Z.to_nat len)). nia.
        * cond_cleanup Hov.
          zstep. (* [comment removed for export] *)
          rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
          zstep. (* [comment removed for export] *)
          zstep. (* [comment removed for export] *)
          rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 3)%Z with 8%Z.
          step. (* [comment removed for export] *)
          (* [comment removed for export] *)
          destruct (Z_of_nat_complete d ltac:(lia)) as [dn Ed].
          destruct (Z_of_nat_complete len1 ltac:(lia)) as [ln El].
          (* [comment removed for export] *)
          pose proof (u64arr_prefix_bytes ASEGS m1 A ws1 ln ltac:(rewrite L1; lia) CUR) as SRC.
          destruct (u64arr_split3 ASEGS m1 A ws1 dn ln ltac:(rewrite L1; lia) CUR) as (U1 & U2 & U3).
          pose proof (u8arr_of_u64arr ASEGS _ _ _ U2) as DST.
          destruct (u64arr_len_split3 ws1 dn ln ltac:(rewrite L1; lia)) as (Ews & Ld & Ll & Lr). rewrite L1 in Lr.
          clear CUR U2.
          pose proof (unsigned_lit (A + d * 8) ltac:(lia)) as UL1. pose proof (unsigned_lit (len1 * 8) ltac:(lia)) as UL2.
          pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as ULs.
          step. (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
            eapply evt_cut; [ eapply asan_memmove_spec with (v := v) (bs := u64s (firstn ln ws1)) (old := u64s (firstn ln (skipn dn ws1)))
                                                          (shlo := (ASAN_B + A / 8 - 8)%Z) (shn := 79%Z)
                            | post_call ASEGS mc ] end.
          all: try side.
          all: try lazymatch goal with
               | |- u8arr _ _ _ _ => ulit; replace (A + d * 8)%Z with (A + 8 * Z.of_nat dn)%Z by lia; exact DST
               | |- length _ = length _ => rewrite !u64s_length, Ll, firstn_length, L1; lia
               | |- Z.of_nat _ = _ => ulit; rewrite u64s_length, firstn_length, L1; lia
               | |- (_ mod _)%Z = _ => ulit; first [rewrite Z_mod_plus_full; exact A8 | apply Z_mod_mult | zlia]
               end.
          name_mem m2. rewrite ?UL1, ?UL2, ?ULs in *.
          match goal with H : u8arr ASEGS m2 (A + d * 8) _ |- _ => rename H into MI2 end.
          pose proof (u64arr_of_u8arr ASEGS m2 (A + d * 8) ln (u64s (firstn ln ws1)) MI2
                        ltac:(rewrite u64s_length, firstn_length, L1; lia)) as MID.
          rewrite words_of_bytes_u64s in MID. replace (A + d * 8)%Z with (A + 8 * Z.of_nat dn)%Z in MID by lia.
          clear MI2.
          assert (Lm : length (firstn ln ws1) = ln) by (rewrite firstn_length, L1; lia).
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          pose proof (unsigned_lit (d * 8) ltac:(lia)) as UL3.
          pose proof (u8arr_of_u64arr ASEGS _ _ _ U1) as DST0.
          step. (* [comment removed for export] *)
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
            eapply evt_cut; [ eapply asan_memset_spec with (v := v) (c := 0%Z) (old := u64s (firstn dn ws1))
                                                         (shlo := (ASAN_B + A / 8 - 8)%Z) (shn := 79%Z)
                            | post_call ASEGS mc ] end.
          all: try side.
          all: try lazymatch goal with
               | |- Z.of_nat _ = _ => ulit; rewrite u64s_length, Ld; lia
               | |- (_ mod _)%Z = _ => zlia
               end.
          name_mem m3. rewrite ?UL3, ?ULs in *.
          match goal with H : u8arr ASEGS m3 A _ |- _ => rename H into MI3 end.
          pose proof (u64arr_of_u8arr ASEGS m3 A dn _ MI3 ltac:(rewrite repeat_length; lia)) as Z1.
          replace (Z.to_nat (d * 8)) with (8 * dn)%nat in Z1 by lia. rewrite words_of_bytes_zero in Z1.
          clear MI3.
          pose proof (u64arr_join3 ASEGS m3 A _ _ _ dn ln (repeat_length _ _) Lm Z1 MID U3) as CUR2.
          set (ws2 := repeat (Z_to_bv 64 0) dn ++ firstn ln ws1 ++ skipn (dn + ln) ws1) in CUR2.
          assert (L2 : length ws2 = 62%nat). { subst ws2. rewrite !app_length, repeat_length, Lm, Lr. lia. }
          clear Z1 MID U3.
          match goal with H : stk ASEGS m3 (bv_unsigned sp - 2272) (bv_unsigned sp + -48) |- _ => rename H into ST3 end.
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          rewrite sx16_lit_small by lia.
          zstep. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          step. (* [comment removed for export] *)
          do 8 step.
          release_frame FR ST3 (bv_unsigned sp).
          unfold shl_post. finish.
          { exact CUR2. } { exact L2. } { exact LENC. } all: try lia.
          intros BN0 CAP _. split; [reflexivity|].
          assert (Hhi : forall j, (j < ln)%nat -> nth (dn + j) ws2 w0 = nth j ws1 w0).
          { intros j Hj. subst ws2. rewrite nth_repeat_app_hi. rewrite app_nth1 by (rewrite Lm; exact Hj).
            rewrite <- (firstn_skipn ln ws1) at 2. rewrite app_nth1 by (rewrite Lm; exact Hj). reflexivity. }
          split.
          -- replace (Z.to_nat (len1 + d)) with (dn + ln)%nat by lia.
             rewrite (bval_shift_limbs ws1 ws2 ln dn).
             ++ replace ln with (Z.to_nat len1) by lia. rewrite VAL.
                rewrite (pow2_split64 n) by lia. rewrite <- Dd, Ed. ring.
             ++ intros j Hj. unfold limbZ. subst ws2. rewrite nth_repeat_app_lo by exact Hj. apply unsigned_lit. lia.
             ++ exact Hhi.
          -- right. replace (Z.to_nat (len1 + d) - 1)%nat with (dn + (ln - 1))%nat by lia.
             unfold limbZ. rewrite Hhi by lia.
             pose proof (bnorm_top ws1 (Z.to_nat len1) ltac:(lia) (BN BN0)) as T. unfold limbZ in T.
             replace (Z.to_nat len1 - 1)%nat with (ln - 1)%nat in T by lia. exact T.
  Qed.
End From.

#[using="shl_bits_spec asan_memmove_spec asan_memset_spec"] Lemma shl_spec : shl_stmt.
Proof. LiaFast.lf_pins (fun (shl_bits_spec asan_memmove_spec asan_memset_spec : LiaFast.U) => LiaFast.u0).
  unfold shl_stmt. intros until v. intros ST AL LIMBS L62 LENC Hlen A8 SEP PRG PRT RTH RD1 RD2 SPLO KSP KSP2 KA0 KA1 SHX RBX.
  pose proof (munch_refl (shl_W (bv_unsigned sp) (bv_unsigned a0)) m) as MU.
  pose proof (wmono_refl ASEGS m) as WM.
  cbv delta [shl_W] in MU.
  pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp.
  pose proof (bv_unsigned_in_range 64 a1) as Rn. unfold bv_modulus in Rn.
  pose proof (u64arr_bound _ _ _ _ LIMBS) as Bl. rewrite L62 in Bl.
  open_RT_keep RTH.
  destruct RTP as (Hbeg & Hblk & Hblk1 & Hctx & Hthr & HFS1 & HFS2 & HFS3 & Hc1 & Hc2 & Ht1 & Ht2 & Hb1 & Hb2).
  (* [comment removed for export] *)
  assert (BC : ro_cells ASEGS m 937400 [C8 (Z_to_bv 64 ASAN_B)]).
  { change [C8 (Z_to_bv 64 ASAN_B); C4 (Z_to_bv 64 1)] with ([C8 (Z_to_bv 64 ASAN_B)] ++ [C4 (Z_to_bv 64 1)]) in RT1.
    apply (proj1 (proj1 (ro_cells_app ASEGS m 937400 _ _) RT1)). }
  clear RT1 RT2 RT2b RT3 RT4 RT5 RT6 RT7 RT8 RT9 RT10 RT11 RT12 RT13 RT14 Hfb fb.
  carve_frame 48%nat ST.
  do 7 step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  name_mem m0.
  step. (* [comment removed for export] *)
  zstep. (* [comment removed for export] *)
  change 63%Z with (Z.ones 6). rewrite Z.land_ones by lia. change (2 ^ 6)%Z with 64%Z.
  step. (* [comment removed for export] *)
  step. (* [comment removed for export] *)
  if_cases Hrem.
  - (* [comment removed for export] *)
    cond_cleanup Hrem.
    eapply shl_from; try eassumption; try lia.
    all: lazymatch goal with
         | |- bval _ _ = _ => rewrite Hrem, Z.pow_0_r; lia
         | |- bnorm _ _ -> bnorm _ _ => intros B; exact B
         | |- munch _ _ _ => cbv delta [shl_W]; exact MU
         end.
  - cond_cleanup Hrem.
    step. (* [comment removed for export] *)
    pose proof (unsigned_lit (bv_unsigned sp + -48) ltac:(lia)) as ULs.
    step. (* [comment removed for export] *)
    pose proof (Z.mod_pos_bound (bv_unsigned a1) 64 ltac:(lia)) as Hmod.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      eapply evt_cut; [ eapply shl_bits_spec with (ws := ws) (len := len) | post_call ASEGS mc ] end.
    all: try side.
    rewrite ?ULs in *.
    (* [comment removed for export] *)
    rename x into b.
    match goal with H : stk ASEGS _ (bv_unsigned sp - 2272) (bv_unsigned sp + -48) |- _ => rename H into ST1 end.
    step. (* [comment removed for export] *)
    if_cases Hb.
    + (* [comment removed for export] *)
      cond_cleanup Hb.
      do 8 step.
      release_frame FR ST1 (bv_unsigned sp).
      unfold shl_post. finish. all: try eassumption. all: try lia.
      intros BN0 CAP _. exfalso.
      rewrite unsigned_lit in * by lia.
      match goal with H : (_ < BIG_CAP)%Z -> b = 1%Z |- _ =>
        enough (b = 1%Z) by lia; apply H end.
      eapply Z.le_lt_trans; [| exact CAP]. apply Z.mul_le_mono_nonneg_l; [apply bval_nonneg|].
      apply Z.pow_le_mono_r; [lia|]. apply Z.mod_le; lia.
    + cond_cleanup Hb.
      rewrite unsigned_lit in * by lia.
      match goal with H : b = 1%Z -> _ |- _ => destruct (H ltac:(lia)) as (VAL1 & LB1 & BN1) end.
      eapply shl_from; try eassumption; try lia.
      all: lazymatch goal with
           | |- bval _ _ = _ => exact VAL1
           | |- bnorm _ _ -> bnorm _ _ => exact BN1
           | |- munch _ _ _ => cbv delta [shl_W]; assumption
           end.
Qed.
End Main.
