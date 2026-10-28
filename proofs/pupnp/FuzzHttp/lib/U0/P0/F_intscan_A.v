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
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_rfile F_intscan_lib.
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

  Lemma L_ret : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 x8 co k c fX,
    finv m -> rw_cells rsegs m Fp (rf_cells T co fX J) -> RFJ' co k c fX -> fX = fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 x8 (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23ce0) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre canary fR HJ. hush.
    intros until fX. intros FI FC RJ EX. subst fX. dest_finv FI.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
    do 13 zs.
    release_frame FR ST q.
    apply evt_done. unfold intscan_post, IS_DEPTH. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact FC|]. split; [exact RJ|]. split; [exact BY | split; [split; [exact SSP1 | exact SSP2]| exact ERR]].
  Qed.

  Lemma L_c48 : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 x8 co k c fX,
    finv m -> rw_cells rsegs m Fp (rf_cells T co fX J) -> RFJ' co k c fX -> fX = fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 x8 (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23cdc) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre canary fR HJ. hush.
    intros until fX. intros FI FC RJ EX. pose proof FI as FI'. dest_finv FI'.
    zs. eapply L_ret; eassumption.
  Qed.

  Lemma L_einval : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 x8 co k c fX,
    finv m -> rw_cells rsegs m Fp (rf_cells T co fX J) -> RFJ' co k c fX -> fX = fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 x8 (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x238ac) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre canary fR Hp SEP SPF SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 HJ. hush.
    intros until fX. intros FI FC RJ EX. pose proof FI as FI'. dest_finv FI'.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
    pose proof (rw_cells_bound _ _ _ _ ERR) as BER. cbn [cells_size csize Nat.add] in BER.
    unfold_fc2 FC.
    zs. callw (eapply errno_callq; [lia | exact MI]).
    zs. zs. zs. zs.
    eapply L_ret; [mk_finv | fc_goal | exact RJ | exact EX].
  Qed.

  Lemma L_rng : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (y neg : word) co k c fX,
    finv m -> rw_cells rsegs m Fp (rf_cells T co fX J) -> RFJ' co k c fX -> fX = fR ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               x18 y neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23c28) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre canary lim fR Hp SEP SPF SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hlim HJ. hush.
    intros until fX. intros FI FC RJ EX. pose proof FI as FI'. dest_finv FI'.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
    pose proof (rw_cells_bound _ _ _ _ ERR) as BER. cbn [cells_size csize Nat.add] in BER.
    unfold_fc2 FC. pose_word_ranges.
    zs. brf K1.
    -
      zs. zs. brf K2.
      +
        zs. brf K3.
        * zs. zs. zs. eapply L_ret; [mk_finv | fc_goal | exact RJ | exact EX].
        * zs. callw (eapply errno_callq; [lia | exact MI]). zs. zs. zs. eapply L_ret; [mk_finv | fc_goal | exact RJ | exact EX].
      + zs. brf K3.
        * zs. brf K4.
          -- zs. zs. zs. eapply L_ret; [mk_finv | fc_goal | exact RJ | exact EX].
          -- zs. callw (eapply errno_callq; [lia | exact MI]). zs. zs. zs. eapply L_ret; [mk_finv | fc_goal | exact RJ | exact EX].
        * zs. callw (eapply errno_callq; [lia | exact MI]). zs. zs. zs. zs. eapply L_ret; [mk_finv | fc_goal | exact RJ | exact EX].
    - zs. zs. zs. eapply L_ret; [mk_finv | fc_goal | exact RJ | exact EX].
  Qed.

  Lemma L_b88 : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (y neg : word) co k c f,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z -> sh_shlim_neg f = false ->
    fR = sh_unget f ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               x18 y neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23c1c) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre canary lim fR Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hlim HJ. hush.
    intros until f. intros FI FC RJ Hk SN HfR. pose proof FI as FI'. dest_finv FI'.
    site_facts FC RJ co k c f.
    pose proof (RFI_unget T txt p J Hp co k c f RJ Hk) as RJu.
    rewrite (rf_unget_eq f SN) in *. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
    zs. zs. zs.
    eapply L_rng; [mk_finv | | exact RJu | symmetry; exact HfR].
    unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
  Qed.

  Lemma L_done : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (y neg : word) co k c f,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    fR = sh_unget f ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               x18 y neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23c14) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre canary lim fR Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hlim HJ. hush.
    intros until f. intros FI FC RJ Hk HfR. pose proof FI as FI'. dest_finv FI'.
    site_facts FC RJ co k c f.
    destruct (sh_shlim_neg f) eqn:SN.
    -
      pose proof (RFI_unget T txt p J Hp co k c f RJ Hk) as RJu.
      rewrite (rf_unget_nop f SN) in *. pose proof FC as FC0. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
      zs. zs. br K1.
      eapply L_rng; [exact FI | exact FC0 | exact RJ | symmetry; exact HfR].
    - pose proof FC as FC0. unfold_fc FC. rewrite SN in FC. unfold M64 in FC.
      zs. zs. br K1.
      eapply L_b88; [exact FI | exact FC0 | exact RJ | exact Hk | exact SN | exact HfR].
  Qed.

  Lemma L_erange : forall m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (y neg : word) co k c f,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    fR = sh_unget f ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               x18 y neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23c70) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre canary lim fR Hp T0 T1 SEP SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hlim HJ. hush.
    intros until f. intros FI FC RJ Hk HfR. pose proof FI as FI'. dest_finv FI'.
    site_facts FC RJ co k c f.
    pose proof (rw_cells_bound _ _ _ _ ERR) as BER. cbn [cells_size csize Nat.add] in BER.
    pose proof (b2z_range (sh_shlim_neg f)) as Rb. pose_word_ranges.
    unfold_fc FC.
    zs. callw (eapply errno_callq; [lia | exact MI]).
    zs. zs. zs. zs. zs. zs.
    destruct (sh_shlim_neg f) eqn:SN; unfold M64 in FC.
    - zs. zs. br K1. zs.
      pose proof (RFI_unget T txt p J Hp co k c f RJ Hk) as RJu. rewrite (rf_unget_nop f SN) in *.
      eapply L_rng; [mk_finv | | exact RJ | symmetry; exact HfR].
      unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
    - zs. zs. br K1.
      eapply L_b88; [mk_finv | | exact RJ | exact Hk | exact SN | exact HfR].
      unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; unfold M64; hyp_cells.
  Qed.

  Lemma L_skip : forall n m (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x24 x28 x29 x30 x31 : word) x1 (y neg : word) co k c f cX fX,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 -> (digval c < base)%Z ->
    is_dig_loop n base (fst (sh_getc f)) (snd (sh_getc f)) = Some (cX, fX) -> fR = sh_unget fX ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) x10 x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) y neg (Z_to_bv 64 0x11984) x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23c4c) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base lim f0 fR ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hlim HJ Q1. hush.
    induction n as [|n IH]; [intros; discriminate|].
    intros until fX. intros FI FC RJ Hk Hst Hc HL HfR.
    assert (Hcnz : c <> 0%Z) by (intros E; rewrite E in Hc; change (digval 0) with 255%Z in Hc; lia).
    pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    cbn [is_dig_loop] in HL.

    assert (DIG : forall c1 f1 co1, sh_getc f = (c1, f1) -> (digval c1 < base)%Z ->
      forall m2 (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x22' x23' x24' x28' x29' x30' x31' : word) x1',
      finv m2 -> rw_cells rsegs m2 Fp (rf_cells T co1 f1 J) -> RFJ' co1 (k + 1) c1 f1 ->
      evt rsegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 lim) (Z_to_bv 64 Fp) x10' x11' x12' x13' x14' x15' x16' x17'
                 (Z_to_bv 64 base) y neg (Z_to_bv 64 0x11984) x22' x23' x24' s9e s10e s11e x28' x29' x30' x31')
            F (Z_to_bv 64 0x23c4c) fc None m2 (seg_rom rsegs))).
    { intros c1 f1 co1 EG Hd. intros. rewrite EG in HL. cbn [fst snd] in HL.
      replace (digval c1 <? base)%Z with true in HL by (symmetry; apply Z.ltb_lt; lia).
      rewrite (surjective_pairing (sh_getc f1)) in HL.
      eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ co1 (k + 1)%Z c1 f1); try eassumption; try LiaTuning.alia.
      rewrite <- Hst. pose proof (stdio_getc f) as X. rewrite EG in X. exact X. }
    assert (ND : forall c1 f1 co1, sh_getc f = (c1, f1) -> ~ (digval c1 < base)%Z ->
      forall m2 (x5' x6' x7' x10' x11' x12' x13' x14' x15' x16' x17' x18' x21' x22' x23' x24' x28' x29' x30' x31' : word) x1',
      finv m2 -> rw_cells rsegs m2 Fp (rf_cells T co1 f1 J) -> RFJ' co1 (k + 1) c1 f1 ->
      evt rsegs POST
        (MS (mkR x1' SPv gp tp x5' x6' x7' (Z_to_bv 64 lim) (Z_to_bv 64 Fp) x10' x11' x12' x13' x14' x15' x16' x17'
                 x18' y neg x21' x22' x23' x24' s9e s10e s11e x28' x29' x30' x31')
            F (Z_to_bv 64 0x23c70) fc None m2 (seg_rom rsegs))).
    { intros c1 f1 co1 EG Hd. intros. rewrite EG in HL. cbn [fst snd] in HL.
      replace (digval c1 <? base)%Z with false in HL by (symmetry; apply Z.ltb_ge; lia).
      injection HL as E1 E2. subst cX fX.
      eapply L_erange with (k := (k + 1)%Z); try eassumption; try LiaTuning.alia. }
    clear IH HL.
    pose proof FI as FI'. dest_finv FI'. site_facts FC RJ co k c f.
    destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T co f)) as [SLOW|FAST].
    -
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. br K.
      destruct (rf_getc_slow T txt p J Hp T1 co k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hco & Hlat & Hc0').
      assert (STD0 : sh_stdio f0 = true) by (rewrite <- Hst; exact STD). destruct (ST0 STD0) as [TXT Hpre].
      pose proof (RFI_getc_slow T txt p J BYT Hp T1 co k c f RJ SLOW) as RJ1.
      zs. zs. callw (eapply shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hpre | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | replace (q + -80 - 160)%Z with (q - 240)%Z by lia; exact ST | plia | plia | plia | plia | plia | plia | plia | plia | plia | exact MI ]).
      post_getc. subst J. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC end.
      assert (Rc1 : (-1 <= fst (sh_getc f) <= 255)%Z) by (destruct RJ1 as (_ & R & _); lia).
      zs.
      table_read (fst (sh_getc f)) Rc1.
      pose proof (digval_byte (fst (sh_getc f))) as Rdv.
      zs. cbv beta. rewrite (unsigned_lit8 (digval (fst (sh_getc f)))) by (apply digval_byte). clear RDt.
      zs. brf K2.
      +   eapply (ND _ _ (win p co) (surjective_pairing _)); [lia | mk_finv | exact FC | exact RJ1].
      + eapply (DIG _ _ (win p co) (surjective_pairing _)); [lia | mk_finv | exact FC | exact RJ1].
    -
      pose proof (RFI_getc T txt p J BYT Hp Hnul co k c f RJ Hcnz FAST) as RJ1.
      pose proof (rf_getc_fast_lt T txt p J Hp co k c f RJ Hcnz FAST) as LT.
      pose proof (rf_getc_fast T txt p J Hp co k c f RJ FAST) as EG.
      rewrite EG in RJ1. cbn [fst snd] in RJ1.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply znth_In; unfold zlength in *; lia)) as Rch. cbv beta in Rch.
      unfold_fc2 FC.
      zs. zs. zs. br K.
      zs. zs.
      pose proof (u8ro_read rsegs _ T (zbytes txt) (sh_rpos f) _ _ BY (zbytes_nth txt (sh_rpos f) ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDb.
      zs. cbv beta. rewrite (unsigned_lit8 (znth txt (sh_rpos f))) by lia. clear RDb.
      zs.
      assert (Rc1 : (-1 <= znth txt (sh_rpos f) <= 255)%Z) by lia. table_read (znth txt (sh_rpos f)) Rc1.
      pose proof (digval_byte (znth txt (sh_rpos f))) as Rdv.
      zs. cbv beta. rewrite (unsigned_lit8 (digval (znth txt (sh_rpos f)))) by (apply digval_byte). clear RDt.
      zs. brf K2.
      + eapply (DIG _ _ co EG); [lia | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | exact RJ1].
      + eapply (ND _ _ co EG); [lia | mk_finv | unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; hyp_cells | exact RJ1].
  Qed.

  Lemma L_b6c : forall n m (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 x28 x29 x30 x31 : word) x1 (y neg : word) co k c f cX fX,
    finv m -> rw_cells rsegs m Fp (rf_cells T co f J) -> RFJ' co k c f -> (1 <= k)%Z ->
    sh_stdio f = sh_stdio f0 ->
    is_dig_loop n base c f = Some (cX, fX) -> fR = sh_unget fX ->
    evt rsegs POST
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 lim) (Z_to_bv 64 Fp) (Z_to_bv 64 c) x11 x12 x13 x14 x15 x16 x17
               (Z_to_bv 64 base) y neg x21 x22 x23 x24 s9e s10e s11e x28 x29 x30 x31)
          F (Z_to_bv 64 0x23c00) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 Fp T p J txt pre post canary base lim f0 fR ST0 BYT Hp Hnul T0 T1 SEP SPLO SPF SPF2 SPT SG1 SG2 SG3 TP SE1 SE2 SE3 SE4 SE5 Hbase Hlim HJ Q1. hush.
    intros until fX. intros FI FC RJ Hk Hst HL HfR.
    destruct n as [|n]; [discriminate|]. cbn [is_dig_loop] in HL.
    pose proof FI as FI'. dest_finv FI'. site_facts FC RJ co k c f.
    assert (Rc1 : (-1 <= c <= 255)%Z) by lia.
    pose proof (digval_byte c) as Rdv. pose_word_ranges.
    zs. zs. zs.
    table_read c Rc1.
    zs. cbv beta. rewrite (unsigned_lit8 (digval c)) by (apply digval_byte). clear RDt.
    zs. brf K1.
    -
      replace (digval c <? base)%Z with true in HL by (symmetry; apply Z.ltb_lt; lia).
      rewrite (surjective_pairing (sh_getc f)) in HL.
      eapply L_skip; [mk_finv | exact FC | exact RJ | exact Hk | exact Hst | lia | exact HL | exact HfR].
    - replace (digval c <? base)%Z with false in HL by (symmetry; apply Z.ltb_ge; lia).
      injection HL as E1 E2. subst cX fX.
      eapply L_done; [mk_finv | exact FC | exact RJ | exact Hk | exact HfR].
  Qed.
End Intscan.
