(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Http Require Import CellConv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr Image.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt ScanIntProps.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy F_memchr Printf_lib F_errno_location.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_rfile F_intscan_lib F_intscan_J F_vfscanf_lib F_vfscanf_A F_vfscanf_B F_vfscanf_C F_vfscanf_D3.
Import ListNotations.
Open Scope Z_scope.
Open Scope bv_scope.

Section Vfscanf.
  Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
  Variables (ra : word) (q : Z) (gp tp : word) (s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e : word)
            (F : bvmap 5 word) (fc : bv 32) (m0 : word -> option byte)
            (T p : Z) (txt pre post : list Z) (canary : word) (P1 P2 P3 FA : Z) (fmtl : list Z) (fuel : nat) (W3num : Z) (w3n : nat) (ap3w : word).
  Hypothesis TXT : rtext T txt pre post.
  Hypothesis Hp : p = zlength pre.
  Hypothesis Hfuel : fuel = S (length txt).
  Hypothesis T0 : (4096 <= T)%Z.
  Hypothesis TW : (T + zlength txt <= 0x2a000 \/ 0x5d000 <= T)%Z.
  Hypothesis T1 : (T + 2^41 <= 2^63)%Z.
  Hypothesis SPLO : (0x5d000 <= q - VF_DEPTH)%Z.
  Hypothesis Q1 : (q + 368 < 2^62)%Z.
  Hypothesis TPV : bv_unsigned tp = 0x3b820%Z.
  Hypothesis SPT : (T + zlength txt <= q - VF_DEPTH \/ q + 368 <= T)%Z.
  Hypothesis HP1 : (0x5d000 <= P1 /\ P1 + 4 <= 2^63)%Z.
  Hypothesis HP2 : (0x5d000 <= P2 /\ P2 + 4 <= 2^63)%Z.
  Hypothesis HP3 : (0x5d000 <= P3 /\ P3 + 4 <= 2^63)%Z.
  Hypothesis HP1q : (P1 + 4 <= q - VF_DEPTH \/ q + 368 <= P1)%Z.
  Hypothesis HP2q : (P2 + 4 <= q - VF_DEPTH \/ q + 368 <= P2)%Z.
  Hypothesis HP3q : (P3 + 4 <= q - VF_DEPTH \/ q + 240 <= P3)%Z.
  Hypothesis HP1t : (P1 + 4 <= T \/ T + zlength txt <= P1)%Z.
  Hypothesis HP2t : (P2 + 4 <= T \/ T + zlength txt <= P2)%Z.
  Hypothesis HP3t : (P3 + 4 <= T \/ T + zlength txt <= P3)%Z.
  Hypothesis HP12 : (P1 + 4 <= P2 \/ P2 + 4 <= P1)%Z.
  Hypothesis HP13 : (P1 + 4 <= P3 \/ P3 + 4 <= P1)%Z.
  Hypothesis HP23 : (P2 + 4 <= P3 \/ P3 + 4 <= P2)%Z.
  Hypothesis HFA : (0x10000 <= FA /\ FA + zlength fmtl <= 0x12000)%Z.
  Hypothesis FMR : Forall (fun c => 0 <= c < 256)%Z fmtl.
  Hypothesis HW3 : (W3num = 2%Z /\ w3n = 0%nat) \/ (W3num = 3%Z /\ w3n = 4%nat).
  Hypothesis HAP3 : W3num = 3%Z -> ap3w = Z_to_bv 64 P3.
  Hypothesis HP3q3 : W3num = 3%Z -> (P3 + 4 <= q - VF_DEPTH \/ q + 368 <= P3)%Z.

  Definition ctx_all : unit :=
    let _ := (ra, q, gp, tp, s0e, s1e, s2e, s3e, s4e, s5e, s6e, s7e, s8e, s9e, s10e, s11e, F, fc, m0, T, p, txt, pre, post, canary, P1, P2, P3, FA, fmtl, fuel, W3num, w3n, ap3w) in
    let _ := (TXT, Hp, Hfuel, T0, TW, T1, SPLO, Q1, TPV, SPT, HP1, HP2, HP3, HP1q, HP2q, HP3q, HP1t, HP2t, HP3t, HP12, HP13, HP23, HFA, FMR, HW3, HAP3, HP3q3) in tt.
  Notation POST := (vf_post ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T txt canary P1 P2 P3 w3n ap3w).
  Notation SPv := (Z_to_bv 64 (q + -480)).
  Notation Fp := (q + 8)%Z.
  Notation AP := (q + 320)%Z.
  Notation RFJ' := (RFJ T txt p ssJ).
  Notation vfinv := (vinv ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 T txt canary P1 P2 P3 FA fmtl w3n ap3w).
  Notation vfinvx := (vinvx ra q s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e m0 T txt canary P1 P2 P3 FA fmtl w3n ap3w).
  Notation LH := (LH_at ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt canary P1 P2 P3 FA fmtl W3num w3n ap3w fuel).

  Lemma Hp2 : (0 <= p < zlength txt)%Z.
  Proof using T p txt pre post TXT Hp. clear -TXT Hp. destruct TXT as (Htxt & _). subst p txt. unfold zlength. rewrite length_app. cbn. lia. Qed.
  Lemma Hnul : znth txt p = 0%Z.
  Proof using T p txt pre post TXT Hp. clear -TXT Hp. destruct TXT as (Htxt & _). subst p txt. rewrite znth_app_r by (unfold zlength; lia). rewrite Z.sub_diag. reflexivity. Qed.
  Lemma BYT : Forall (fun c => 0 <= c < 256)%Z txt.
  Proof using T txt pre post TXT. clear -TXT. destruct TXT as (_ & _ & B & _). exact B. Qed.
  Lemma Hpre : forall i, (0 <= i < p)%Z -> znth txt i <> 0%Z.
  Proof using T p txt pre post TXT Hp.
    clear -TXT Hp. intros i Hi. destruct TXT as (Htxt & NZ & _). subst p txt. rewrite znth_app_l by exact Hi.
    pose proof (proj1 (Forall_forall _ _) NZ (znth pre i) (znth_In pre i Hi)). cbv beta in H. lia.
  Qed.
  Lemma L40 : (zlength txt <= 2^40)%Z.
  Proof using T txt pre post TXT. clear -TXT. destruct TXT as (_ & _ & _ & _ & L). exact L. Qed.
  Lemma HW3le : (W3num <= 3)%Z /\ (w3n <= 4)%nat.
  Proof using W3num w3n HW3. clear -HW3. lia. Qed.

  Lemma getc_nz : forall co k c f, RFJ' co k c f -> sh_stdio f = true -> fst (sh_getc f) <> 0%Z.
  Proof using T p txt pre post TXT Hp.
    clear -TXT Hp. intros co k c f (OK & Rc & CC & KM & NS & SS) ST. destruct OK as (Hbuf & _). destruct (SS ST) as (Hn & Hr & _).
    unfold sh_getc. rewrite ST. cbn [negb]. destruct (Z.eqb_spec (sh_rpos f) (sh_n f)); cbn [negb fst]; [lia|].
    rewrite Hbuf. apply Hpre. destruct CC. lia.
  Qed.

  Definition hidden2 (P : Prop) := P.
  Ltac stash2 H := lazymatch type of H with hidden2 _ => idtac | ?T => change T with (hidden2 T) in H end.
  Ltac unstash := unfold hidden, hidden2 in *.
  Ltac lia1h := first [ lia
    | unfold hidden2 in SPT; lia | unfold hidden2 in TW; lia
    | unfold hidden2 in HP1q; lia | unfold hidden2 in HP2q; lia | unfold hidden2 in HP3q; lia
    | unfold hidden2 in HP3q3; unfold hidden in HW3; lia ].
  Ltac lia1f := first [ lia1h | unfold hidden, hidden2 in *; lia ].
  Ltac djsolve := first [ exact I | lia1h | split; [lia1h | djsolve] ].
  Local Ltac slia ::= djsolve.

  Ltac dest_vinv H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
    let j16 := fresh "j16" in let j32 := fresh "j32" in let j40 := fresh "j40" in let j56 := fresh "j56" in let j64 := fresh "j64" in let j72 := fresh "j72" in
    let LOW := fresh "LOW" in let scs := fresh "scs" in let SCS := fresh "SCS" in let HI := fresh "HI" in
    let ST := fresh "ST" in let BY := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    let ev := fresh "ev" in let ERR := fresh "ERR" in let APC := fresh "APC" in
    let v1 := fresh "v1" in let v2 := fresh "v2" in let v3 := fresh "v3" in let PC1 := fresh "PC1" in let PC2 := fresh "PC2" in let PC3 := fresh "PC3" in let FMB := fresh "FMB" in
    destruct H as (MI & MU & WM & (j16 & j32 & j40 & j56 & j64 & j72 & LOW) & (scs & SCS) & HI & ST & BY & [SSP1 SSP2] & [ev ERR] & APC & (v1 & v2 & v3 & PC1 & PC2 & PC3) & FMB);
    unfold vlow in LOW; unfold vhi in HI; unfold vf_FP, VF_DEPTH, ERRNOA in MU; unfold VF_DEPTH in ST; unfold ERRNOA in ERR;
    unfold got_ssp, ssp_guard in SSP1, SSP2, LOW;
    unfold VF_DEPTH in SPLO, SPT, HP1q, HP2q, HP3q;
    try (let LT := fresh "LTX" in pose proof (zbytes_length txt) as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
    try (let LF := fresh "LTF" in pose proof (zbytes_length fmtl) as LF; lazymatch goal with _ : length (zbytes fmtl) = length fmtl, _ : length (zbytes fmtl) = length fmtl |- _ => clear LF | _ => idtac end);
    unfold zlength in *.
  Ltac dest_vinvx H := let MI := fresh "MI" in let MU := fresh "MU" in let WM := fresh "WM" in
    let j16 := fresh "j16" in let j32 := fresh "j32" in let j40 := fresh "j40" in let j56 := fresh "j56" in let j64 := fresh "j64" in let j72 := fresh "j72" in
    let LOW := fresh "LOW" in let scs := fresh "scs" in let SCS := fresh "SCS" in let HI := fresh "HI" in
    let ST := fresh "ST" in let BY := fresh "BY" in let SSP1 := fresh "SSP1" in let SSP2 := fresh "SSP2" in
    let ev := fresh "ev" in let ERR := fresh "ERR" in let APC := fresh "APC" in
    let v1 := fresh "v1" in let v2 := fresh "v2" in let v3 := fresh "v3" in let PC1 := fresh "PC1" in let PC2 := fresh "PC2" in let PC3 := fresh "PC3" in let FMB := fresh "FMB" in
    destruct H as (MI & MU & WM & (j16 & j56 & j72 & LOW) & (scs & SCS) & HI & ST & BY & [SSP1 SSP2] & [ev ERR] & APC & (v1 & v2 & v3 & PC1 & PC2 & PC3) & FMB);
    unfold vlow in LOW; unfold vhi in HI; unfold vf_FP, VF_DEPTH, ERRNOA in MU; unfold VF_DEPTH in ST; unfold ERRNOA in ERR;
    unfold got_ssp, ssp_guard in SSP1, SSP2, LOW;
    unfold VF_DEPTH in SPLO, SPT, HP1q, HP2q, HP3q;
    try (let LT := fresh "LTX" in pose proof (zbytes_length txt) as LT; lazymatch goal with _ : length (zbytes txt) = length txt, _ : length (zbytes txt) = length txt |- _ => clear LT | _ => idtac end);
    try (let LF := fresh "LTF" in pose proof (zbytes_length fmtl) as LF; lazymatch goal with _ : length (zbytes fmtl) = length fmtl, _ : length (zbytes fmtl) = length fmtl |- _ => clear LF | _ => idtac end);
    unfold zlength in *.
  Ltac mk_vinv := unfold vinv, vinvx, vlow, vhi, vf_FP, VF_DEPTH, ERRNOA, ssp_cells, got_ssp, ssp_guard;
    repeat match goal with |- _ /\ _ => split | |- ex _ => eexists end; first [hyp | hyp_cells].
  Ltac unfold_fc FC := unfold rf_cells, rf_rend in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC;
    unfold STRING_READ, M64 in FC.
  Ltac unfold_fc2 FC := unfold rf_cells in FC;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale] in FC;
    unfold STRING_READ, M64 in FC.
  Ltac plia := unfold zlength, got_ssp, ssp_guard, VF_DEPTH in *; lia1f.
  Ltac fc_goal := unfold rf_cells, rf_rend;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
    unfold STRING_READ, M64 in *; first [hyp | hyp_cells].
  Ltac fc_goal2 := unfold rf_cells;
    cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
    unfold STRING_READ, M64 in *; first [hyp | hyp_cells].

  Ltac conv_cells H l := apply (rw_cells_conv_sel0 l) in H; cbn [conv_sel conv8 existsb Nat.eqb orb] in H.
  Ltac conv_cell H i := conv_cells H [i].

  Ltac hush := stash HP1t; stash HP2t; stash HP3t; stash HP12; stash HP13; stash HP23; stash HW3;
    try stash2 TW; try stash2 SPT; try stash2 HP1q; try stash2 HP2q; try stash2 HP3q; try stash2 HAP3; try stash2 HP3q3;
    lazymatch goal with _ : (W3num <= 3)%Z /\ (w3n <= 4)%nat |- _ => idtac | _ => pose proof HW3le as NCM end.
  Ltac zs := zstep; try (fix_litstore; mem_after_store_opt).

  Ltac post_getc :=
    match goal with H : ssp_cells ?m' _ |- _ =>
      repeat match goal with H2 : rw_cells _ _ 172368 _ |- _ => clear H2 | H2 : rw_cells _ _ 375432 _ |- _ => clear H2 end;
      destruct H as [SSP1' SSP2']; unfold got_ssp, ssp_guard in SSP1', SSP2' end;
    match goal with H : stk _ ?m' (q + -480 - 160)%Z _ |- _ =>
      try match goal with H2 : stk _ _ (q - 720)%Z (q + -480)%Z |- _ => tryif constr_eq H H2 then fail else clear H2 end end;
    repeat match goal with H : bytes_at _ ?m' T ?x, H2 : bytes_at _ ?m' T ?x |- _ => clear H2 end.

  Ltac site_facts FC RJ co k c f :=
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC; cbn [cells_size csize Nat.add rf_cells] in BFC;
    pose proof RJ as RJ2; destruct RJ2 as (OK & Rc & CC & KM & NS & SS); destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst);
    assert (RR : (0 <= rf_rend T co f <= M64)%Z) by (unfold rf_rend, M64; destruct (sh_stdio f) eqn:?STQ; [destruct (SS eq_refl) as (? & ? & ?)|]; unfold zlength in *; lia); unfold M64 in RR;
    pose proof (RFI_rpos T txt p ssJ Hp2 co k c f RJ) as Rrp.

  Lemma L_dirW : forall ds', LH ds' ->
    forall m (i : Z) f co k c (mt na : Z) r (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word),
    vfinv na mt m -> rw_cells rsegs m Fp (rf_cells T co f ssJ) -> RFJ' co k c f -> (0 <= k)%Z -> c <> 0%Z -> sh_stdio f = true ->
    fmt_enc (skipn (Z.to_nat i) fmtl) (SW :: ds') -> (0 <= i)%Z ->
    (0 <= mt <= na)%Z -> (na + nconv (SW :: ds') <= W3num)%Z ->
    vfs fuel (SW :: ds') f mt = Some r ->
    evt rsegs (POST r)
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 31) (Z_to_bv 64 37) (Z_to_bv 64 (FA + i)) x22 x23 (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x200c4) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. exact (@F_vfscanf_B.L_dirW ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3). Qed.

  Lemma L_dirL : forall ch ds', LH ds' ->
    forall m (i : Z) f co k c (mt na : Z) r (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word),
    vfinv na mt m -> rw_cells rsegs m Fp (rf_cells T co f ssJ) -> RFJ' co k c f -> (0 <= k)%Z -> c <> 0%Z -> sh_stdio f = true ->
    fmt_enc (skipn (Z.to_nat i) fmtl) (SL ch :: ds') -> (0 <= i)%Z ->
    (0 <= mt <= na)%Z -> (na + nconv (SL ch :: ds') <= W3num)%Z ->
    vfs fuel (SL ch :: ds') f mt = Some r ->
    evt rsegs (POST r)
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 31) (Z_to_bv 64 37) (Z_to_bv 64 (FA + i)) x22 x23 (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x200c4) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. exact (@F_vfscanf_C.L_dirL ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3). Qed.

  Lemma L_dirD : forall ds', LH ds' ->
    forall m (i : Z) f co k c (mt na : Z) r (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word) she shl shc,
    vfinv na mt m -> rw_cells rsegs m Fp (rf_cells_raw T co f ssJ she shl shc) -> RFJ' co k c f -> (0 <= k)%Z -> c <> 0%Z -> sh_stdio f = true ->
    fmt_enc (skipn (Z.to_nat i) fmtl) (SD :: ds') -> (0 <= i)%Z ->
    (0 <= mt <= na)%Z -> (na + nconv (SD :: ds') <= W3num)%Z ->
    vfs fuel (SD :: ds') f mt = Some r ->
    evt rsegs (POST r)
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 31) (Z_to_bv 64 37) (Z_to_bv 64 (FA + i)) x22 x23 (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x200c4) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. exact (@F_vfscanf_D3.L_dirD ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3). Qed.

  Lemma L_9b4 : forall m (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) x1 co f
      (apw j16 j32 j40 j56 j64 : word) (mt : Z) j72 scs ev v1 v2 v3,
    mem_inv rsegs m -> munch (vf_FP q P1 P2 P3) m0 m -> wmono rsegs m0 m ->
    rw_cells rsegs m (q + -480) (vlow apw j16 j32 j40 mt j56 j64 j72) -> rw_cells rsegs m (q + -368) [CB 256 scs] ->
    rw_cells rsegs m (q + -112) (vhi canary ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) ->
    stk rsegs m (q - VF_DEPTH) (q + -480) -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
    rw_cells rsegs m ERRNOA [C4 ev] -> rw_cells rsegs m AP [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w] ->
    rw_cells rsegs m P1 [C4 v1] -> rw_cells rsegs m P2 [C4 v2] -> rw_cells rsegs m P3 [CB w3n v3] ->
    rw_cells rsegs m Fp (rf_cells T co f ssJ) -> (0 <= mt < 2^31)%Z ->
    evt rsegs (POST mt)
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x20a48) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. exact (@F_vfscanf_A.L_9b4 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3). Qed.

  Ltac rd_fmt FMB i := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u8ro_read rsegs mm FA (zbytes fmtl) i _ _ FMB (zbytes_nth fmtl i ltac:(unfold zlength in *; lia)) ltac:(lia) eq_refl) as RDf end.

  Lemma L_nul :
    forall m (i : Z) f co k c (mt na : Z) r (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x27 x28 x29 x30 x31 : word),
    vfinv na mt m -> rw_cells rsegs m Fp (rf_cells T co f ssJ) -> RFJ' co k c f -> (0 <= k)%Z -> c <> 0%Z -> sh_stdio f = true ->
    fmt_enc (skipn (Z.to_nat i) fmtl) [] -> (0 <= i)%Z ->
    (0 <= mt <= na)%Z -> (na + nconv [] <= W3num)%Z ->
    vfs fuel [] f mt = Some r ->
    evt rsegs (POST r)
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 31) (Z_to_bv 64 37) (Z_to_bv 64 (FA + i)) x22 x23 (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x200c4) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. pose proof ctx_all as Hctx_all.
    intros until x31. intros FI FC RJ Hk Hcnz Hst FE Hi Hmt Hna HV.
    cbn [fmt_enc] in FE. destruct (skipn (Z.to_nat i) fmtl) as [|b0 l1] eqn:E0; [destruct FE|].
    destruct (Z.eq_dec b0 0) as [Eb0|]; [|exfalso; destruct b0 as [|pp|pp]; try exact FE; repeat (destruct pp; try exact FE); lia]. subst b0.
    destruct (skipn_cons_znth _ _ _ _ E0) as (Zi & El1 & LT0). rewrite Z2Nat.id in Zi by lia.
    cbn [vfs] in HV. injection HV as <-.
    pose proof FI as FI'. dest_vinv FI'. site_facts FC RJ co k c f. hush.
    pose_word_ranges.
    rd_fmt FMB i. zs. cbv beta. rewrite (unsigned_lit8 (znth fmtl i)) by (rewrite Zi; lia). clear RDf. rewrite Zi.
    zs. br K1. zs. zs. brf K2; [| exfalso; clear - K2; cbv in K2; discriminate K2]. zs. br K3.
    eapply L_9b4; try eassumption. { split; assumption. } cbn [nconv] in Hna. lia.
  Qed.

  Lemma L_loop : forall ds, LH ds.
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. pose proof ctx_all as Hctx_all.
    induction ds as [|d ds IH]; unfold LH_at; intros until x31; intros FI FC RJ Hk Hcnz Hst FE Hi Hmt Hna HV.
    - eapply L_nul; eassumption.
    - destruct d as [| |ch].
      + rewrite rf_cells_raw_eq in FC. eapply (L_dirD ds IH); eassumption.
      + eapply (L_dirW ds IH); eassumption.
      + eapply (L_dirL ch ds IH); eassumption.
  Qed.

  Lemma L_VA : forall ds' (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (ev v1 v2 : word) (v3 : list byte) r,
    stk rsegs m0 (q - VF_DEPTH) q -> mem_inv rsegs m0 ->
    rw_cells rsegs m0 Fp (ss_cells T 0 0 w0 T 0 w0 w0) ->
    rw_cells rsegs m0 AP [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w] ->
    rw_cells rsegs m0 P1 [C4 v1] -> rw_cells rsegs m0 P2 [C4 v2] -> rw_cells rsegs m0 P3 [CB w3n v3] ->
    bytes_at rsegs m0 T (zbytes txt) -> ssp_cells m0 canary -> rw_cells rsegs m0 ERRNOA [C4 ev] ->
    bytes_at rsegs m0 FA (zbytes fmtl) -> fmt_enc fmtl (SD :: ds') -> (nconv (SD :: ds') <= W3num)%Z ->
    sscanf_model (SD :: ds') txt p = Some r ->
    evt rsegs (POST r)
      (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0e s1e (Z_to_bv 64 Fp) (Z_to_bv 64 FA) (Z_to_bv 64 AP) a3 a4 a5 a6 a7
               s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e t3 t4 t5 t6)
          F (Z_to_bv 64 VFSCANF) fc None m0 (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. pose proof ctx_all as Hctx_all.
    intros until r. intros ST MI FC APC PC1 PC2 PC3 BY [SSP1 SSP2] ERR FMB FE HNC HV.
    pose proof (munch_refl (vf_FP q P1 P2 P3) m0) as MU. pose proof (wmono_refl rsegs m0) as WM.
    unfold vf_FP, VF_DEPTH, ERRNOA in MU. unfold VF_DEPTH in ST. unfold ERRNOA in ERR. unfold got_ssp, ssp_guard in SSP1, SSP2.
    unfold VF_DEPTH in SPLO, SPT, HP1q, HP2q, HP3q. hush.
    pose proof (zbytes_length txt) as LTX. pose proof (zbytes_length fmtl) as LTF. pose proof Hp2 as Hp'. unfold zlength in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as BFC. unfold ss_cells in BFC. cbn [cells_size csize Nat.add] in BFC.
    pose proof (rw_cells_bound _ _ _ _ ERR) as BER. cbn [cells_size csize Nat.add] in BER.
    pose proof FC as FC0. unfold ss_cells, w0, zero4 in FC0. unfold STRING_READ, M64 in FC0.
    unfold sscanf_model in HV. rewrite <- Hfuel in HV.
    pose_word_ranges.
    unfold VFSCANF.

    zs. carve_frame 112%nat ST. rename FR into FRhi.
    carve_frame 256%nat ST. rename FR into SCS.
    carve_frame 112%nat ST. rename FR into LOW.
    apply (rw_cells_split_CB _ _ _ [] 112 _ [] [8;8;8;8;8;8;8;8;8;40]%nat) in LOW; [|reflexivity]. cbn [mk_CB_cells app] in LOW.
    conv_cells LOW [0;1;2;3;4;5;6;7;8]%nat.
    repeat match type of LOW with context [le_bytes_to_word ?b] => let w := fresh "jw" in set (w := le_bytes_to_word b) in LOW; clearbody w end.
    repeat match goal with H : list byte |- _ => lazymatch goal with _ : rw_cells _ _ _ [CB 256 H] |- _ => fail | _ => clear H end end.
    do 13 zs.

    zs. zs. zs. zs. zs. zs.

    zs. rewrite ?sx32_M64. zs. zs. br K1.
    zs. zs. zs. br K2.
    pose proof toread_spec as TR. unfold toread_stmt in TR.
    match goal with H : stk _ ?mm _ _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      destruct (stk_split _ _ _ (q + -480 - 16)%Z _ H ltac:(lia)) as [STlo SThi]; clear H end.
    zs. zs. callw (eapply TR with (Fp := Fp) (T := T) (rpos := 0%Z) (rend := 0%Z) (cookie := T) (shend := 0%Z) (mode := w0) (shl := w0) (shc := w0);
      [ unfold ss_cells, w0, zero4; unfold STRING_READ, M64; hyp | left; reflexivity | lia | lia | lia | lia | lia
      | replace (q + -480 - 16)%Z with (q + -480 - 16)%Z by lia; exact SThi | lia | lia | lia | lia | lia | assumption ]).
    clear TR.
    match goal with H : rw_cells _ ?mm Fp (ss_cells _ _ _ _ _ _ _ _) |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into FC1 end.
    match goal with H : stk _ ?mm (q + -480 - 16)%Z _ |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (stk_merge _ _ _ _ _ STlo H ltac:(lia)) as ST; clear STlo H end.
    pose proof FC1 as FC2. unfold ss_cells, w0, zero4 in FC2. unfold STRING_READ, M64 in FC2.
    zs. zs. br K3.

    zs. zs. zs. zs. zs. zs. zs. zs. zs. zs.
    match goal with |- ?g => idtac "ATLOOP"; idtac g end.

    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FC3 : rw_cells rsegs mm Fp (rf_cells_raw T 0 (ssf0 txt p) ssJ (Z_to_bv 64 0) w0 w0))
        by (unfold rf_cells_raw, rf_rend, ssf0, w0; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg ssJ j_flags j_pad0 j_close j_wend j_wpos j_mbz1 j_wbase j_read j_write j_seek j_bufsize j_prev j_next j_fd j_ppid j_lockcount j_mode j_lock j_lbf j_pad1 j_cookie j_off j_getln j_mbz2 j_pl j_nl j_locale];
            unfold STRING_READ, M64 in *; first [hyp | hyp_cells]) end.
    assert (RJ0 : RFJ' 0 0 1 (ssf0 txt p)).
    { unfold RFJ, sh_ok, ssf0. cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]. pose proof L40. unfold zlength in *.
      repeat split; try reflexivity; try lia; try (intros X; discriminate X). }
    let v := getreg 21%Z in replace v with (Z_to_bv 64 (FA + 0)) by (f_equal; lia).
    eapply (L_dirD ds' (L_loop ds') _ 0%Z (ssf0 txt p) 0%Z 0%Z 1%Z 0%Z 0%Z r);
      [ mk_vinv | exact FC3 | exact RJ0 | lia | lia | reflexivity | cbn [skipn Z.to_nat]; exact FE | lia | lia | lia | exact HV ].
  Qed.

End Vfscanf.
