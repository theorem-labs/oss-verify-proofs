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
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_rfile F_intscan_lib F_intscan_A F_intscan_C F_intscan_E F_intscan_G.
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

  Lemma L_einval : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 x8 co k c fX,
    finv m -> rw_cells rsegs m Fp (rf_cells T co fX J) -> RFJ' co k c fX -> fX = fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 x8 (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x238ac) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt post canary fR Hp SEP SPF SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 HJ. hush. intros; eapply F_intscan_A.L_einval; eassumption. Qed.

  Lemma L_b10 : forall n m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (neg : word) co k c f cX fX,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> base = 10%Z -> (48 <= c <= 57)%Z ->
    is_dig_loop n base (fst (sh_getc f)) (snd (sh_getc f)) = Some (cX, fX) -> fR = sh_unget fX ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) x19 neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x238d8) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base pok lim fuel f0 fR HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hlim HJ Q1. hush. intros; eapply F_intscan_C.L_b10; eassumption. Qed.

  Lemma L_p16 : forall n m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (neg : word) co k c f cX fX,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> base = 16%Z ->
    is_dig_loop n base c f = Some (cX, fX) -> fR = sh_unget fX ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) x19 neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23a04) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base lim f0 fR ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hlim HJ Q1. hush. intros; eapply F_intscan_E.L_p16; eassumption. Qed.

  Lemma L_79c : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (neg : word) co k c f,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z -> c <> 0%Z ->
    sh_stdio f = sh_stdio f0 -> base = 16%Z ->
    (let '(c2, f2) := sh_getc f in
     if (Z.lor c2 32 =? 120)%Z then
       let '(c3, f3) := sh_getc f2 in
       if (16 <=? digval c3)%Z then Some (if nz pok then sh_unget (sh_unget f3) else sh_lim0 (sh_unget f3)) else is_digits fuel 16 c3 f3
     else is_digits fuel 16 c2 f2) = Some fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) (Z_to_bv 64 pok) neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23830) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base pok lim fuel f0 fR ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hpok Hlim HJ Q1. hush. intros; eapply F_intscan_G.L_79c; eassumption. Qed.

  Definition after_sign (c : Z) (f : shfile) : option shfile :=
    if ((base =? 16) && (c =? 48))%Z then
      let '(c2, f2) := sh_getc f in
      if (Z.lor c2 32 =? 120)%Z then
        let '(c3, f3) := sh_getc f2 in
        if (16 <=? digval c3)%Z then Some (if nz pok then sh_unget (sh_unget f3) else sh_lim0 (sh_unget f3)) else is_digits fuel 16 c3 f3
      else is_digits fuel 16 c2 f2
    else if (base <=? digval c)%Z then Some (sh_lim0 (sh_unget f))
    else is_digits fuel base c f.

  Lemma L_7dc : forall m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (neg : word) co k c f,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 ->
    (if (base <=? digval c)%Z then Some (sh_lim0 (sh_unget f)) else is_digits fuel base c f) = Some fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) (Z_to_bv 64 pok) neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23870) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base pok lim fuel f0 fR HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hlim HJ Q1. hush.
    intros until f. intros FI FC RJ Hk Hst HT. pose proof FI as FI'. dest_finv FI'. site_facts FC RJ co k c f.
    assert (Rc1 : (-1 <= c <= 255)%Z) by lia. pose proof (digval_byte c) as Rdv. pose_word_ranges.
    zs. br K0.
    zs. zs. zs. table_read c Rc1.
    zs. cbv beta. rewrite (unsigned_lit8 (digval c)) by (apply digval_byte). clear RDt.
    zs. brf K1.
    -
      replace (base <=? digval c)%Z with false in HT by (symmetry; apply Z.leb_gt; lia).
      destruct Hbase as [Hb | Hb].
      +
        unfold is_digits in HT. remember fuel as fu eqn:EF in HT. destruct fu as [|n]; [discriminate|]. cbn [is_dig_loop] in HT.
        replace (digval c <? base)%Z with true in HT by (symmetry; apply Z.ltb_lt; lia).
        rewrite (surjective_pairing (sh_getc f)) in HT.
        destruct (is_dig_loop n base (fst (sh_getc f)) (snd (sh_getc f))) as [[cX fX]|] eqn:HL; [|discriminate]. injection HT as HfR.
        assert (Hd : (48 <= c <= 57)%Z) by (apply (proj1 (digval_lt10 c)); lia).
        eapply L_b10; [exact FI | exact FC | exact RJ | exact Hk | exact Hst | exact Hb | exact Hd | exact HL | symmetry; exact HfR].
      +
        replace (Z_to_bv 64 base) with (Z_to_bv 64 16) by (rewrite Hb; reflexivity).
        zs. zs. br K2.
        unfold is_digits in HT. destruct (is_dig_loop fuel base c f) as [[cX fX]|] eqn:HL; [|discriminate]. injection HT as HfR.
        replace (Z_to_bv 64 16) with (Z_to_bv 64 base) by (rewrite Hb; reflexivity).
        eapply L_p16; [exact FI | exact FC | exact RJ | exact Hk | exact Hst | exact Hb | exact HL | symmetry; exact HfR].
    -
      replace (base <=? digval c)%Z with true in HT by (symmetry; apply Z.leb_le; lia). injection HT as HfR.
      pose proof (RFI_unget T txt p J Hp co k c f RJ Hk) as RJu.
      pose proof (RFI_lim0 T txt p J Hp co (k - 1) c (sh_unget f) RJu) as RJl.
      destruct HJ as [HJ0 HJ1].
      pose proof shlim_spec as SL. unfold shlim_stmt in SL.
      destruct (sh_shlim_neg f) eqn:SN.
      + rewrite (rf_unget_nop f SN) in *. pose proof FC as FC0. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
        zs. zs. br K2.
        rewrite rf_cells_raw_eq in FC0.
        zs. zs. zs. callw (eapply SL with (txt := txt); [exact FC0 | exact (RFI_ok T txt p J co k c f RJ) | exact HJ0 | exact HJ1 | lia | lia | | exact MI];
                            intros STD; destruct (SS STD) as (_ & X & _); unfold zlength in *; lia).
        clear SL. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC1 end.
        eapply L_einval; [mk_finv | exact FC1 | exact RJl | exact HfR].
      + rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
        zs. zs. br K2.
        zs. zs. zs.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m1 _) =>
          assert (FC0 : rw_cells rsegs m1 Fp (rf_cells_raw T co (mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) J
                         (Z_to_bv 64 (rf_rend T co f)) (Z_to_bv 64 0) (Z_to_bv 64 (- sh_cnt0 f))))
            by (unfold rf_cells_raw, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells) end.
        zs. zs. zs. callw (eapply SL with (txt := txt); [exact FC0 | | exact HJ0 | exact HJ1 | lia | lia | | exact MI];
                            [ destruct (RFI_ok T txt p J co k c f RJ) as (B1 & B2 & B3 & B4 & B5 & B6); unfold sh_ok; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; repeat split; try assumption; try lia; intros STD; specialize (B6 STD); lia
                            | cbn [sh_stdio]; intros STD; destruct (SS STD) as (_ & X & _); unfold zlength in *; lia ]).
        clear SL. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC1 end.
        eapply L_einval; [mk_finv | exact FC1 | exact RJl | exact HfR].
  Qed.

  Lemma L_794 : forall m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (neg : word) co k c f,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> base = 16%Z ->
    after_sign c f = Some fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) (Z_to_bv 64 pok) neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23828) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base pok lim fuel f0 fR HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hpok Hlim HJ Q1. hush.
    intros until f. intros FI FC RJ Hk Hst Hb HT. pose proof FI as FI'. dest_finv FI'. site_facts FC RJ co k c f.
    pose_word_ranges. unfold after_sign in HT. rewrite Hb in HT. cbn [Z.eqb Pos.eqb andb] in HT.
    zs. zs. brf K1.
    - replace (c =? 48)%Z with false in HT by (symmetry; apply Z.eqb_neq; mlia2). rewrite <- Hb in HT.
      eapply L_7dc; [exact FI | exact FC | exact RJ | exact Hk | exact Hst | exact HT].
    - replace (c =? 48)%Z with true in HT by (symmetry; apply Z.eqb_eq; mlia2).
      eapply L_79c; [exact FI | exact FC | exact RJ | exact Hk | mlia2 | exact Hst | exact Hb | exact HT].
  Qed.

  Lemma L_7dc' : forall m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (neg : word) co k c f,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> base = 10%Z ->
    after_sign c f = Some fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) (Z_to_bv 64 pok) neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23870) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base pok lim fuel f0 fR HM ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hlim HJ Q1. hush.
    intros until f. intros FI FC RJ Hk Hst Hb HT. unfold after_sign in HT. rewrite Hb in HT. cbn [Z.eqb Pos.eqb andb] in HT. rewrite <- Hb in HT.
    eapply L_7dc; eassumption.
  Qed.

End Intscan.
