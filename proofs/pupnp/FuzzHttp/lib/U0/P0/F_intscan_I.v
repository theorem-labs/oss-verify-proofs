(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy F_memchr Printf_lib F_errno_location.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_rfile F_intscan_lib F_intscan_H.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Section Intscan.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
            (Fp T p : Z) (J : rfj) (txt pre post : list Z) (canary : word) (base pok lim : Z) (fuel : nat)
            (f0 : shfile) (co0 kmin0 c0 : Z) (fR : shfile).
  Hypothesis HM : intscan fuel base pok f0 = Some fR.
  Hypothesis ST0 : sh_stdio f0 = true -> rtext T txt pre post /\ p = zlength pre.
  Hypothesis BYT : Forall (fun c => 0 <= c < 256)%Z txt.
  Hypothesis Hp : (0 <= p < zlength txt)%Z.
  Hypothesis Hnul : znth txt p = 0%Z.
  Hypothesis T0 : (4096 <= T)%Z.
  Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
  Hypothesis SEP : (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z.
  Hypothesis SPLO : (4096 <= q - IS_DEPTH)%Z.
  Hypothesis SPF : (q <= Fp)%Z.
  Hypothesis SPF2 : (Fp + 232 <= 2^63)%Z.
  Hypothesis SPT : (T + zlength txt <= q - IS_DEPTH \/ q <= T)%Z.
  Hypothesis SG1 : (ssp_guard + 8 <= q - IS_DEPTH)%Z.
  Hypothesis SG2 : (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z.
  Hypothesis SG3 : (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z.
  Hypothesis TP : (4096 + 164 <= bv_unsigned tp)%Z.
  Hypothesis SE1 : (ERRNO tp + 4 <= q - IS_DEPTH \/ q <= ERRNO tp)%Z.
  Hypothesis SE2 : (ERRNO tp + 4 <= Fp \/ Fp + 232 <= ERRNO tp)%Z.
  Hypothesis SE3 : (ERRNO tp + 4 <= T \/ T + zlength txt <= ERRNO tp)%Z.
  Hypothesis SE4 : (ERRNO tp + 4 <= got_ssp \/ got_ssp + 8 <= ERRNO tp)%Z.
  Hypothesis SE5 : (ERRNO tp + 4 <= ssp_guard \/ ssp_guard + 8 <= ERRNO tp)%Z.
  Hypothesis Hbase : (base = 10 \/ base = 16)%Z.
  Hypothesis Hpok : (0 <= pok <= 1)%Z.
  Hypothesis Hlim : (0 <= lim < 2^64)%Z.
  Hypothesis HJ : length (j_pad0 J) = 4%nat /\ length (j_pad1 J) = 4%nat.
  Hypothesis Q1 : (q < 2^63)%Z.

  Notation POST := (intscan_post ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt canary fR).
  Notation SPv := (Z_to_bv 64 (q + -80)).
  Notation RFJ' := (RFJ T txt p J).
  Notation finv := (is_finv ra q tp s0e s1e s2e s3e s4e s5e s6e s7e s8e m0 Fp T txt canary).

  Definition hidden (P : Prop) := P.
  Ltac stash H := lazymatch type of H with hidden _ => idtac | ?T => change T with (hidden T) in H end.
  Ltac unhide := unfold hidden in *.
  Ltac hush := try stash SEP; try stash SPT; try stash SG2; try stash SG3; try stash SE1; try stash SE2; try stash SE3; try stash SE4; try stash SE5.
  Ltac lia1h := first [ lia
    | unfold hidden in SPT; lia | unfold hidden in SEP; lia | unfold hidden in SE1; lia | unfold hidden in SE2; lia | unfold hidden in SE3; lia
    | unfold hidden in SG2; lia | unfold hidden in SG3; lia | unfold hidden in SE4; lia | unfold hidden in SE5; lia ].
  Ltac lia1f := first [ lia1h | unhide; lia ].
  Ltac djsolve := first [ exact I | lia1h | split; [lia1h | djsolve] ].
  Local Ltac slia ::= djsolve.

  Ltac dest_finv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in let FR := fresh "FR" in
    let ST := fresh "ST" in let BY := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    let ev := fresh "ev" in let ERR := fresh "ERR" in
    destruct H as (MI & MU & WM & FR & ST & BY & [SSP1 SSP2] & [ev ERR]); unfold is_frame in FR; unfold is_W, IS_DEPTH in MU; unfold IS_DEPTH in ST;
    unfold got_ssp, ssp_guard in SSP1, SSP2;
    unfold IS_DEPTH, got_ssp, ssp_guard in SPLO, SPT, SG1, SG2, SG3, SE1, SE2, SE3, SE4, SE5;
    try (let LT := fresh "LTX" in pose proof (zbytes_length txt) as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
    unfold zlength in *.
  Ltac mk_finv := unfold is_finv, is_frame, is_W, IS_DEPTH, ssp_cells, got_ssp, ssp_guard;
    split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [hyp|]; split; [split; hyp|]; eexists; hyp.
  Ltac unfold_fc FC := unfold rf_cells, rf_rend in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  Ltac unfold_fc2 FC := unfold rf_cells in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC.
  Ltac plia := unfold zlength, got_ssp, ssp_guard, IS_DEPTH in *; lia1f.

  Ltac table_read c Hc :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) =>
      match goal with H : mem_inv _ m |- _ => pose proof (istab_read m c _ H Hc eq_refl) as RDt end end.

  Ltac fixd c := rewrite ?swrap32_landW, ?swrap32_landW_sub; rewrite (swrap32_small (c + -48)) by lia.

  Ltac fc_goal := unfold rf_cells, rf_rend;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
    unfold M64 in *; first [hyp | hyp_cells].

  Ltac post_getc :=
    match goal with H : ssp_cells ?m' _ |- _ =>
      repeat match goal with H2 : rw_cells _ _ 172368 _ |- _ => clear H2 | H2 : rw_cells _ _ 375432 _ |- _ => clear H2 end;
      destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end;
    match goal with H : stk _ ?m' (q + -80 - 160)%Z _ |- _ =>
      replace (q + -80 - 160)%Z with (q - 240)%Z in H by lia;
      try match goal with H2 : stk _ _ (q - 240)%Z _ |- _ => tryif constr_eq H H2 then fail else clear H2 end end;
    repeat match goal with H : bytes_at _ ?m' T ?x, H2 : bytes_at _ ?m' T ?x |- _ => clear H2 end.

  Ltac site_facts FC RJ co k c f :=
    unfold IS_DEPTH, got_ssp, ssp_guard in SPLO, SPT, SG1, SG2, SG3, SE1, SE2, SE3, SE4, SE5;
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
    pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
    assert (RR : (0 <= rf_rend T co f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f); unfold zlength in *; lia); unfold M64 in RR;
    pose proof (RFI_rpos T txt p J Hp co k c f RJ) as Rrp.

  Notation after_sign := (F_intscan_H.after_sign base pok fuel).

  Lemma L_794 : forall m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (neg : word) co k c f,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> base = 16%Z ->
    after_sign c f = Some fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) (Z_to_bv 64 pok) neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23828) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base pok lim fuel f0 fR HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hpok Hlim HJ Q1. hush. intros; eapply F_intscan_H.L_794; eassumption. Qed.

  Lemma L_7dc' : forall m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (neg : word) co k c f,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> base = 10%Z ->
    after_sign c f = Some fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) (Z_to_bv 64 pok) neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23870) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base pok lim fuel f0 fR HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hlim HJ Q1. hush. intros; eapply F_intscan_H.L_7dc'; eassumption. Qed.

  Lemma isspace_iff : forall c, (-1 <= c <= 255)%Z -> (m_isspace c = true <-> (c = 32 \/ 9 <= c <= 13))%Z.
  Proof using Type. hush. clear. intros c Hc. apply m_isspace_iff. lia. Qed.

  Lemma L_734 : forall m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 co k c f,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 ->
    (let '(c2, f2) := (if ((c =? 43) || (c =? 45))%Z then sh_getc f else (c, f)) in after_sign c2 f2) = Some fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) (Z_to_bv 64 pok) x20 x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x237c8) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base pok lim fuel f0 fR HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hpok Hlim HJ Q1. hush.
    intros until f. intros FI FC RJ Hk Hst HT. pose proof FI as FI'. dest_finv FI'. site_facts FC RJ co k c f.
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    pose_word_ranges.

    assert (TAIL : forall pc co1 k1 c1 f1 m2 (x5' x6' x7' x11' x12' x13' x14' x15' x16' x17' x21' x22' x23' x24' x28' x29' x30' x31' : word) x1' (neg : word),
      (pc = 0x237fc \/ pc = 0x2380c \/ pc = 0x23820)%Z ->
      finv m2 -> rw_cells rsegs m2 Fp (rf_cells T co1 f1 J) -> RFJ' co1 k1 c1 f1 -> (1 <= k1)%Z -> sh_stdio f1 = sh_stdio f0 ->
      after_sign c1 f1 = Some fR ->
      evt rsegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 lim) (Z_to_bv 64 Fp) (Z_to_bv 64 c1) x11' x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 base) (Z_to_bv 64 pok) neg x21' x22' x23' x24' s9e s10e s11e x28' x29' x30' x31')
            F (Z_to_bv 64 pc) fc None m2 (seg_rom rsegs))).
    { intros until neg. intros Hpc FI2 FC2 RJ2 Hk1 Hst2 HT2. pose proof FI2 as FI''. dest_finv FI''.
      destruct Hbase as [Hb | Hb].
      - replace (Z_to_bv 64 base) with (Z_to_bv 64 10) by (rewrite Hb; reflexivity).
        destruct Hpc as [-> | [-> | ->]]; [zs; zs; br KT; zs | zs; zs; br KT; zs | zs; zs; br KT];
          replace (Z_to_bv 64 10) with (Z_to_bv 64 base) by (rewrite Hb; reflexivity);
          (eapply L_7dc'; [exact FI2 | exact FC2 | exact RJ2 | exact Hk1 | exact Hst2 | exact Hb | exact HT2]).
      - replace (Z_to_bv 64 base) with (Z_to_bv 64 16) by (rewrite Hb; reflexivity).
        destruct Hpc as [-> | [-> | ->]]; zs; zs; br KT;
          replace (Z_to_bv 64 16) with (Z_to_bv 64 base) by (rewrite Hb; reflexivity);
          (eapply L_794; [exact FI2 | exact FC2 | exact RJ2 | exact Hk1 | exact Hst2 | exact Hb | exact HT2]). }
    zs. zs. brf K1.
    -
      replace (((c =? 43) || (c =? 45))%Z) with true in HT by (symmetry; apply Bool.orb_true_intro; right; apply Z.eqb_eq; mlia2).
      assert (Hcnz : c <> 0%Z) by mlia2.
      rewrite (surjective_pairing (sh_getc f)) in HT.
      destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T co f)) as [SLOW|FAST].
      * pose proof FC as FC0. unfold_fc2 FC.
        zs. zs. zs. zs. zs. zs. br K.
        destruct (rf_getc_slow T txt p J Hp T1 co k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hco & Hlat & Hc0').
        assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
        pose proof (RFI_getc_slow T txt p J BYT Hp T1 co k c f RJ SLOW) as RJ1.
        zs. zs. callw (eapply shgetc_callJ;
          [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
          | plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
        post_getc. rewrite <- EJ in *. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
        eapply TAIL; [right; right; reflexivity | mk_finv | exact FC | exact RJ1 | lia | exact Hst1 | exact HT].
      * pose proof (RFI_getc T txt p J BYT Hp Hnul co k c f RJ Hcnz FAST) as RJ1.
        pose proof (rf_getc_fast_lt T txt p J Hp co k c f RJ Hcnz FAST) as LT.
        pose proof (rf_getc_fast T txt p J Hp co k c f RJ FAST) as EG.
        rewrite EG in RJ1, HT, Hst1. cbn [fst snd] in RJ1, HT, Hst1.
        pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply znth_In; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
        unfold_fc2 FC.
        zs. zs. zs. zs. zs. zs. br K.
        zs. zs.
        pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
        zs. cbv beta. rewrite (unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
        eapply TAIL; [left; reflexivity | mk_finv | | exact RJ1 | lia | exact Hst1 | exact HT]. fc_goal.
    -
      zs. zs. brf K2.
      +
        replace (((c =? 43) || (c =? 45))%Z) with false in HT by (symmetry; apply Bool.orb_false_intro; apply Z.eqb_neq; mlia2).
        zs. eapply TAIL; [right; left; reflexivity | exact FI | exact FC | exact RJ | exact Hk | exact Hst | exact HT].
      +
        replace (((c =? 43) || (c =? 45))%Z) with true in HT by (symmetry; apply Bool.orb_true_intro; left; apply Z.eqb_eq; mlia2).
        assert (Hcnz : c <> 0%Z) by mlia2.
        rewrite (surjective_pairing (sh_getc f)) in HT.
        destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T co f)) as [SLOW|FAST].
        * pose proof FC as FC0. unfold_fc2 FC.
          zs. zs. zs. zs. zs. zs. br K.
          destruct (rf_getc_slow T txt p J Hp T1 co k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hco & Hlat & Hc0').
          assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
          pose proof (RFI_getc_slow T txt p J BYT Hp T1 co k c f RJ SLOW) as RJ1.
          zs. zs. callw (eapply shgetc_callJ;
            [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
            | plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
          post_getc. rewrite <- EJ in *. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
          eapply TAIL; [right; right; reflexivity | mk_finv | exact FC | exact RJ1 | lia | exact Hst1 | exact HT].
        * pose proof (RFI_getc T txt p J BYT Hp Hnul co k c f RJ Hcnz FAST) as RJ1.
          pose proof (rf_getc_fast_lt T txt p J Hp co k c f RJ Hcnz FAST) as LT.
          pose proof (rf_getc_fast T txt p J Hp co k c f RJ FAST) as EG.
          rewrite EG in RJ1, HT, Hst1. cbn [fst snd] in RJ1, HT, Hst1.
          pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply znth_In; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
          unfold_fc2 FC.
          zs. zs. zs. zs. zs. zs. br K.
          zs. zs.
          pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
          zs. cbv beta. rewrite (unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
          eapply TAIL; [left; reflexivity | mk_finv | | exact RJ1 | lia | exact Hst1 | exact HT]. fc_goal.
  Qed.

End Intscan.
