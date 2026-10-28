(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run Fs.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import StrFun StrFun2.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac CellConv.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_ctype F_syscalls F_errno_location F_strtol F_atoi F_htons F_memset F_memmove F_stpncpy F_strncasecmp
     F_inet_pton_A F_inet_pton_C H_parse_uric H_memptr_cmp H_parse_uri_A H_parse_uri_B HU_puri_B2 HU_list_kit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Set Printing Width 1000.
Set Printing Depth 100.

Notation HTTPS := 0x106e8%Z.
Definition https6 : list byte := map (Z_to_bv 8) [104; 116; 116; 112; 115; 0]%Z.
Lemma https_bytes : forall m, mem_inv rsegs m -> bytes_at rsegs m HTTPS https6.
Proof.
  intros m MI. pose proof (ro_cells_image rsegs m HTTPS https6 MI ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(cbn; lia)) as RO.
  destruct RO as [_ B]. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B. exact B.
Qed.

Lemma land64_mod : forall x, Z.land x 18446744073709551615 = (x mod 2^64)%Z.
Proof. intros x. change 18446744073709551615%Z with (Z.ones 64). apply Z.land_ones. lia. Qed.

Lemma land64_inj_neg : forall a b, (-2^31 <= a < 2^31 -> -2^31 <= b < 2^31 ->
  Z.land a 18446744073709551615 = Z.land b 18446744073709551615 -> a = b)%Z.
Proof.
  intros a b Ha Hb E. change 18446744073709551615%Z with (Z.ones 64) in E. rewrite !Z.land_ones in E by lia.
  exact (mod64_inj_signed a b Ha Hb E).
Qed.

Section WALK.
Context {HCEIL : HasCeiling}.
  Variables (U O ulen : Z) (ustr slack : list byte) (canary gifv : word).
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Hypothesis USL : Z.of_nat (length ustr) = ulen.
  Hypothesis ULR : (0 <= ulen < 2^31)%Z.
  Hypothesis PAD : ((- (U + ulen + 1)) mod 8 <= Z.of_nat (length slack))%Z.
  Hypothesis U4K : (4096 <= U)%Z.
  Hypothesis ULO : (U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 928)%Z.
  Hypothesis OSP : (bv_unsigned sp <= O)%Z.
  Hypothesis OHI : (O + 216 <= 2^62)%Z.
  Hypothesis OAL : oal O.
  Hypothesis SPH : (bv_unsigned sp + 2^41 <= 2^63)%Z.
  Hypothesis TP1 : (4096 + 164 <= bv_unsigned tp)%Z.
  Hypothesis TP2 : (bv_unsigned tp - 164 + 4 <= bv_unsigned sp - 928)%Z.
  Hypothesis SGLO : (ssp_guard + 8 <= bv_unsigned sp - 928)%Z.
  Hypothesis GSLO : (got_ssp + 8 <= bv_unsigned sp - 928)%Z.
  Hypothesis GFLO : (GIF + 4 <= bv_unsigned sp - 928)%Z.
  Hypothesis DE1 : (bv_unsigned tp - 164 + 4 <= got_ssp \/ got_ssp + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE2 : (bv_unsigned tp - 164 + 4 <= ssp_guard \/ ssp_guard + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE3 : (bv_unsigned tp - 164 + 4 <= GOT_GIF \/ GOT_GIF + 8 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE4 : (bv_unsigned tp - 164 + 4 <= GIF \/ GIF + 4 <= bv_unsigned tp - 164)%Z.
  Hypothesis DE5 : (bv_unsigned tp - 164 + 4 <= U \/ U + ulen + 1 + Z.of_nat (length slack) <= bv_unsigned tp - 164)%Z.

  Notation SP := (bv_unsigned sp).
  Notation q := (bv_unsigned sp + -400)%Z.
  Notation spw := (Z_to_bv 64 (bv_unsigned sp + -400)).
  Notation lo := (bv_unsigned sp - 928)%Z.
  Notation TPE := (bv_unsigned tp - 164)%Z.
  Notation W := [(bv_unsigned sp - 928, bv_unsigned sp); (O, O + 216); (bv_unsigned tp - 164, bv_unsigned tp - 164 + 4)]%Z.
  Notation POST := (parse_uri_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc U O ustr slack canary gifv m0).
  Notation USTR m := (bytes_at rsegs m U (ustr ++ Z_to_bv 8 0 :: slack)).

  Notation baseP := (base U O ustr slack canary gifv sp tp m0).

  Notation FRB m := (rw_cells rsegs m (q + 296) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).

  Ltac open_base B :=
    let errv := fresh "errv" in
    destruct B as (USTR & [errv ERR] & GOT & CAN & GIFP & GIFV & MI & MU & WM).
  Ltac close_base :=
      split; [assumption|]; split; [eexists; eassumption|]; repeat (split; [assumption|]); assumption.

  #[using="U ulen slack ULR U4K ULO SPH"] Lemma sp_rangeC : (928 <= SP /\ SP + 2^41 <= 2^63)%Z.
  Proof. clear -ULR U4K ULO SPH. pose proof (word_lt64 sp). lia. Qed.
  #[using="U ulen ustr slack ULR U4K ULO SPH GFLO"] Lemma q_spC : bv_unsigned spw = q.
  Proof. pose proof sp_rangeC. apply unsigned_lit. lia. Qed.
  #[using="USL"] Lemma nth_UC : forall i, (0 <= i <= ulen)%Z -> exists b, nth_error (ustr ++ Z_to_bv 8 0 :: slack) (Z.to_nat i) = Some b.
  Proof.
    clear -USL. intros i Hi. destruct (nth_error _ (Z.to_nat i)) as [b|] eqn:E; [eexists; reflexivity|].
    apply nth_error_None in E. rewrite length_app in E. cbn [length] in E. lia.
  Qed.
  #[using="USL"] Lemma USTR_lenC : Z.of_nat (length (ustr ++ Z_to_bv 8 0 :: slack)) = (ulen + 1 + Z.of_nat (length slack))%Z.
  Proof. clear -USL. rewrite length_app. cbn [length]. lia. Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE3 DE4"] Lemma nohp : forall (bh : Z) m jA junk
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 296 jA] -> FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O [CB 216 junk] -> (0 <= bh <= ulen)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 1) (Z_to_bv 64 bh) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16d48) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros B FRA FRBm ST OUT BH.
    pose proof sp_rangeC as SR. pose proof q_spC as QSP. open_base B.
    pose proof (rw_cells_split_CB rsegs m O [] 216 junk [] [64; 152]%nat OUT eq_refl) as OUT'. cbn [mk_CB_cells app] in OUT'. clear OUT.
    lazymatch type of OUT' with rw_cells _ _ _ [?a; ?b] => change (rw_cells rsegs m O ([a] ++ [b])) in OUT' end.
    apply rw_cells_app in OUT'. destruct OUT' as [OL HP]. cbn [cells_size csize Nat.add] in HP. change (Z.of_nat 64) with 64%Z in HP.
    zstep. zstep. zstep. zstep.
    lazymatch type of HP with rw_cells _ _ _ [CB _ ?h] => call (memset0_call (O + 64) 152 h) end.
    all: side (first [exact HP | assumption | reflexivity | lia]).
    match goal with H : rw_cells _ _ (O + 64)%Z _ |- _ => rename H into HP end. change (Z.to_nat 152) with 152%nat in HP.
    replace (O + 64 + 152)%Z with (O + 216)%Z in * by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
      destruct (out_join2 O m' _ _ OL eq_refl HP eq_refl) as [junk' OUT] end.
    eapply tail; try eassumption; try LiaTuning.alia. close_base.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma slash : forall (bh a0v is5 : Z) m jA junk
      x1 x5 x6 x7 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x27 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 296 jA] -> FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O [CB 216 junk] ->
    (0 <= bh)%Z -> (bh + 1 < ulen)%Z -> (0 <= a0v < 2^64)%Z -> (0 <= is5 < 2^64)%Z -> (is5 <> 0 -> a0v = U /\ 5 <= ulen)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) (Z_to_bv 64 a0v) (Z_to_bv 64 is5) (Z_to_bv 64 (bh + 1)) x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 x21 x22 x23 x24 (Z_to_bv 64 1) (Z_to_bv 64 bh) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16cb0) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros B FRA FRBm ST OUT BH0 BH1 A0 I5 HS.
    pose proof sp_rangeC as SR. pose proof q_spC as QSP. open_base B. pose proof USTR_lenC as UL.
    destruct (nth_UC bh ltac:(lia)) as [b0 Hb0]. pose proof (byte_range b0) as BR0.
    pose proof (u8ro_read rsegs m U _ bh b0 (Z_to_bv 64 (U + bh)) USTR Hb0 ltac:(lia) eq_refl) as RD0.
    destruct (nth_UC (bh + 1) ltac:(lia)) as [b1 Hb1]. pose proof (byte_range b1) as BR1.
    pose proof (u8ro_read rsegs m U _ (bh + 1) b1 (Z_to_bv 64 (U + (bh + 1))) USTR Hb1 ltac:(lia) eq_refl) as RD1.
    uwalk_ub_to 0x16d48%Z.
    if_cases K0; zify_cond K0.
    {   eapply nohp; try eassumption; try LiaTuning.alia. close_base. }
    uwalk_ub_to 0x16d48%Z.
    if_cases K1; zify_cond K1.
    {   eapply nohp; try eassumption; try LiaTuning.alia. close_base. }
    pose proof (rw_cells_split_CB rsegs m q [] 296 jA [] [32; 8; 256]%nat FRA eq_refl) as FRA'. cbn [mk_CB_cells app] in FRA'. clear FRA.
    lazymatch type of FRA' with rw_cells _ _ _ [?c0; CB 8 ?b; ?c2] => pose proof (rw_cells_CB_C8 rsegs m q [c0] b [c2] FRA') as FRA end.
    cbn [app] in FRA. clear FRA'.
    uwalk_ub_to 0x16e4c%Z.
    if_cases K2; zify_cond K2.
    {   uwalk_ub_to 0x16e4c%Z.
        eapply hp with (bh2 := (bh + 2)%Z) (defport := 80%Z); try eassumption; try LiaTuning.alia. close_base. }
    destruct (HS ltac:(lia)) as [-> UL5].
    zstep. zstep. zstep. zstep.
    pose proof (https_bytes _ MI) as HB6.
    destruct (strncasecmp_model_some (map (Z_to_bv 8) [104; 116; 116; 112; 115]%Z) (ustr ++ Z_to_bv 8 0 :: slack) [] 5 ltac:(lia) ltac:(lia)) as (v & HM & HV).
    change (map (Z_to_bv 8) [104; 116; 116; 112; 115]%Z ++ [Z_to_bv 8 0]) with https6 in HM.
    callq (strncasecmp_call q lo U HTTPS 5 v (ustr ++ Z_to_bv 8 0 :: slack) https6).
    all: side (first [exact HB6 | exact HM | exact ST | assumption | reflexivity | (cbn [https6 map length]; lia) | lia]).
    match goal with H : stk _ _ lo q |- _ => rename H into ST' end.
    zstep. if_cases K3; zify_cond K3.
    -   uwalk_ub_to 0x16e4c%Z.
        eapply hp with (bh2 := (bh + 2)%Z) (defport := 443%Z); try eassumption; try LiaTuning.alia. close_base.
    - uwalk_ub_to 0x16e4c%Z.
      eapply hp with (bh2 := (bh + 2)%Z) (defport := 80%Z); try eassumption; try LiaTuning.alia. close_base.
  Qed.

  #[using="Type"] Lemma out_forget4 : forall m c0 c1 c2 c3 c4 c5, rw_cells rsegs m O [c0; c1; c2; c3; c4; c5] -> cells_size [c0; c1; c2; c3; c4; c5] = 216%nat ->
    exists junk, rw_cells rsegs m O [CB 216 junk].
  Proof. intros m c0 c1 c2 c3 c4 c5 H L. destruct (rw_cells_forget rsegs m O _ H) as [j J]. rewrite L in J. exists j. exact J. Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma failsch : forall m jA (oa ob : list byte) (w1 w2 : word)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 296 jA] -> FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O [CB 8 oa; C8 w1; C8 w2; CB 192 ob] ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16c8c) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros B FRA FRBm ST OUT.
    pose proof sp_rangeC as SR. pose proof q_spC as QSP. open_base B.
    assert (S9 : Z.b2z (0 <? U) = 1%Z) by (destruct (Z.ltb_spec 0 U); [reflexivity| lia]).
    zstep. zstep. zstep. zstep. sstep. sstep. zstep. zstep. zstep. rewrite ?S9. if_cases K0; zify_cond K0.
    -
      lazymatch goal with OUT : rw_cells _ ?m' O [?c0; ?c1; ?c2; ?c3; ?c4; ?c5] |- _ =>
        destruct (out_forget4 m' c0 c1 c2 c3 c4 c5 OUT eq_refl) as [junk OUT'] end.
      eapply nohp; try eassumption; try LiaTuning.alia. close_base.
    - lazymatch goal with OUT : rw_cells _ ?m' O [?c0; ?c1; ?c2; ?c3; ?c4; ?c5] |- _ =>
        destruct (out_forget4 m' c0 c1 c2 c3 c4 c5 OUT eq_refl) as [junk OUT'] end.
      eapply (slash 0 0 0); try eassumption; try LiaTuning.alia. close_base.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma foundsch : forall (i e10 : Z) m jA (oa ob : list byte) (w1 w2 : word)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x20 x21 x22 x23 x24 x25 x27 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 296 jA] -> FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O [CB 8 oa; C8 w1; C8 w2; CB 192 ob] ->
    (1 <= i < ulen)%Z -> (e10 = i + 1)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 x20 x21 x22 x23 x24 x25 (Z_to_bv 64 e10) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16d18) fc None m (seg_rom rsegs)).
  Proof.
    intros until x31. intros B FRA FRBm ST OUT I E4.
    pose proof sp_rangeC as SR. pose proof q_spC as QSP. open_base B.
    pwalk_to 0x16d44%Z.
    assert (S9 : Z.b2z (0 <? U) = 1%Z) by (destruct (Z.ltb_spec 0 U); [reflexivity| lia]). rewrite S9.
    match goal with |- context [Z_to_bv 64 (Z.b2z ?b)] =>
      set (is5 := Z.b2z b);
      assert (I5 : (0 <= is5 < 2^64)%Z) by (subst is5; destruct b; cbn; lia);
      assert (I5b : is5 <> 0%Z -> (e10 = 6)%Z)
        by (subst is5; destruct b eqn:Eb; [intros _| intros C; exfalso; apply C; reflexivity];
            apply Z.ltb_lt in Eb; rewrite land64_mod in Eb; clear -Eb I E4 ULR; Z.div_mod_to_equations; lia);
      clearbody is5 end.
    step. if_cases K0; zify_cond K0.
    -
      lazymatch goal with OUT : rw_cells _ ?m' O [?c0; ?c1; ?c2; ?c3; ?c4; ?c5] |- _ =>
        destruct (out_forget4 m' c0 c1 c2 c3 c4 c5 OUT eq_refl) as [junk OUT'] end.
      eapply (slash e10 U is5); try eassumption; try LiaTuning.alia.
      all: try (intros H5; specialize (I5b H5); split; [reflexivity| lia]).
      all: close_base.
    - lazymatch goal with OUT : rw_cells _ ?m' O [?c0; ?c1; ?c2; ?c3; ?c4; ?c5] |- _ =>
        destruct (out_forget4 m' c0 c1 c2 c3 c4 c5 OUT eq_refl) as [junk OUT'] end.
      eapply nohp; try eassumption; try LiaTuning.alia. close_base.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma schloop : forall m jA (oa ob : list byte) (w1 w2 : word) (e8 e9 : Z) (k : nat) (i e10 : Z)
      x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x27 x28 x29 x30 x31,
    baseP m -> rw_cells rsegs m q [CB 296 jA] -> FRB m -> stk rsegs m lo q ->
    rw_cells rsegs m O [CB 8 oa; C8 w1; C8 w2; CB 192 ob] ->
    (e8 = 1 - ulen)%Z -> (e9 = 114349209288704)%Z ->
    (ulen - i < Z.of_nat k)%Z -> (1 <= i < ulen)%Z -> (e10 = i + 1)%Z ->
    evt rsegs POST (MS (mkR x1 spw gp tp x5 x6 x7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 U) x19 (Z_to_bv 64 (U + 1)) (Z_to_bv 64 2) (Z_to_bv 64 58) (Z_to_bv 64 46) (Z_to_bv 64 e8) (Z_to_bv 64 e9) (Z_to_bv 64 e10) x27 x28 x29 x30 x31)
                        F (Z_to_bv 64 0x16c54) fc None m (seg_rom rsegs)).
  Proof.
    intros until k. induction k as [|k IH]; intros until x31; intros B FRA FRBm ST OUT E8 E9 HK I E10; [lia|]. subst e10.
    pose proof sp_rangeC as SR. pose proof q_spC as QSP. pose proof B as B0. open_base B. pose proof USTR_lenC as UL.
    destruct (nth_UC i ltac:(lia)) as [b Hb]. pose proof (byte_range b) as BR.
    pose proof (u8ro_read rsegs m U _ i b (Z_to_bv 64 (U + i)) USTR Hb ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. zstep. step. ubr.
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    {   eapply (foundsch i (i + 1)%Z); try eassumption; try LiaTuning.alia. }
    step. ubr.
    zstep. zstep. call isalnum_spec. all: side (rewrite ?unsigned_lit by lia; first [assumption | lia]).
    rewrite unsigned_lit by lia.

    assert (NEXT : forall y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
      evt rsegs POST (MS (mkR (Z_to_bv 64 0x16c78) spw gp tp y5 y6 y7 (Z_to_bv 64 O) (Z_to_bv 64 ulen) y10 y11 y12 y13 y14 y15 y16 y17
                            (Z_to_bv 64 U) (Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 64 (U + 1)) (Z_to_bv 64 2) (Z_to_bv 64 58) (Z_to_bv 64 46) (Z_to_bv 64 e8) (Z_to_bv 64 e9) (Z_to_bv 64 (i + 1)) x27 y28 y29 y30 y31)
                        F (Z_to_bv 64 0x16c48) fc None m (seg_rom rsegs))).
    { intros until y31. zstep. zstep. zstep. if_cases K1; zify_cond K1.
      -   eapply failsch; try eassumption.
      - assert (i + 1 <> ulen)%Z by (intros C; apply K1; rewrite ?land64_mod; Z.div_mod_to_equations; lia).
        eapply (IH (i + 1)%Z); try eassumption; try LiaTuning.alia. }
    zstep. if_cases K2; zify_cond K2.
    {   apply NEXT. }
    zstep. if_cases K3; zify_cond K3.
    {   eapply failsch; try eassumption. }
    zstep. zstep. zstep. if_cases K4; zify_cond K4.
    {   apply NEXT. }
    eapply failsch; try eassumption.
  Qed.

  #[using="USL ULR PAD U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5"] Lemma body : forall x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31 junk errv,
    USTR m0 -> rw_cells rsegs m0 O [CB 216 junk] -> rw_cells rsegs m0 TPE [C4 errv] ->
    rw_cells rsegs m0 got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells rsegs m0 ssp_guard [C8 canary] ->
    bytes_at rsegs m0 GOT_GIF (le8 (Z_to_bv 64 GIF)) -> bytes_at rsegs m0 GIF (le4 gifv) ->
    stk rsegs m0 lo SP -> mem_inv rsegs m0 ->
    evt rsegs POST (MS (mkR ra sp gp tp x5 x6 x7 s0 s1 (Z_to_bv 64 U) (Z_to_bv 64 ulen) (Z_to_bv 64 O) x13 x14 x15 x16 x17
                            s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                        F (Z_to_bv 64 parse_uri_entry) fc None m0 (seg_rom rsegs)).
  Proof.
    intros until errv. intros USTR0 OUT ERR GOT CAN GIFP0 GIFV0 ST MI. unfold parse_uri_entry.
    pose proof sp_rangeC as SR. pose proof q_spC as QSP. pose proof USTR_lenC as UL.
    assert (GIFP : ro_cells rsegs m0 GOT_GIF [C8 (Z_to_bv 64 GIF)]). { split; [cbn; LiaTuning.ctauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact GIFP0. }
    assert (GIFV : ro_cells rsegs m0 GIF [C4 gifv]). { split; [cbn; LiaTuning.ctauto|]. cbn [cells_bytes cbytes]. rewrite app_nil_r. exact GIFV0. }
    clear GIFP0 GIFV0.
    pose proof (munch_refl W m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
    pose proof (rw_cells_bound _ _ _ _ OUT) as OB. cbn [cells_size csize Nat.add] in OB.
    carve_frame 400%nat ST. pose proof OAL as OA. unfold oal in OA.
    pwalk_to 0x16bfc%Z.
    lazymatch goal with H : rw_cells _ ?m' q (CB 296 ?jA :: ?rest) |- _ =>
      change (rw_cells rsegs m' q ([CB 296 jA] ++ rest)) in H; apply rw_cells_app in H; destruct H as [FRA FRBm];
      cbn [cells_size csize Nat.add] in FRBm; change (Z.of_nat 296) with 296%Z in FRBm end.
    pwalk_to 0x16c54%Z.
    if_cases K1; zify_cond K1.
    {   eapply failsch; try eassumption. close_base. }
    destruct (nth_UC 0 ltac:(lia)) as [b0 Hb0]. pose proof (byte_range b0) as BR0.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m' _) =>
      pose proof (u8ro_read rsegs m' U _ 0 b0 (Z_to_bv 64 U) USTR0 Hb0 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD end.
    pwalk_to 0x16c54%Z. if_cases K2; zify_cond K2.
    {   eapply failsch; try eassumption. close_base. }
    pwalk_to 0x16c54%Z. if_cases K3; zify_cond K3.
    {   eapply failsch; try eassumption. close_base. }
    pwalk_to 0x16c54%Z.
    eapply (schloop _ _ _ _ _ _ _ _ (S (Z.to_nat ulen)) 1 2); try eassumption; try reflexivity; try lia. close_base.
  Qed.
End WALK.

Lemma parse_uri_spec : parse_uri_stmt.
Proof.
  unfold parse_uri_stmt, PURI_DEPTH. intros until m.
  intros USTR USL ULR PAD OUT ERR GOT CAN GIFP GIFV ST MI U4K ULO OSP OHI OAL SPH TP1 TP2 SGLO GSLO GFLO DE1 DE2 DE3 DE4 DE5 -> -> ->.
  eapply body; eauto.
Qed.
