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
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import F_rfile F_intscan_lib F_intscan_J F_vfscanf_lib F_vfscanf_A F_vfscanf_D1.
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

  Lemma L_9c8 : forall m (x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word) x1 co f
      (apw j16 j40 j56 j64 : word) (mt : Z) j72 scs ev v1 v2 v3,
    mem_inv rsegs m -> munch (vf_FP q P1 P2 P3) m0 m -> wmono rsegs m0 m ->
    rw_cells rsegs m (q + -480) (vlow apw j16 (Z_to_bv 64 0) j40 mt j56 j64 j72) -> rw_cells rsegs m (q + -368) [CB 256 scs] ->
    rw_cells rsegs m (q + -112) (vhi canary ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) ->
    stk rsegs m (q - VF_DEPTH) (q + -480) -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
    rw_cells rsegs m ERRNOA [C4 ev] -> rw_cells rsegs m AP [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w] ->
    rw_cells rsegs m P1 [C4 v1] -> rw_cells rsegs m P2 [C4 v2] -> rw_cells rsegs m P3 [CB w3n v3] ->
    rw_cells rsegs m Fp (rf_cells T co f ssJ) -> (0 <= mt < 2^31)%Z ->
    evt rsegs (POST (if mt =? 0 then -1 else mt)%Z)
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) x9 x10 x11 x12 x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x20a5c) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. exact (@F_vfscanf_A.L_9c8 ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3). Qed.

  Lemma L_65c : forall ds', LH ds' ->
    forall m (i : Z) f co k c (mt na : Z) r (x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x18 x27 x28 x29 x30 x31 : word) (xw : word) j16 j56 j72,
    mem_inv rsegs m -> munch (vf_FP q P1 P2 P3) m0 m -> wmono rsegs m0 m ->
    rw_cells rsegs m (q + -480) (vlow (Z_to_bv 64 (AP + 8 * (na + 1))) j16 (Z_to_bv 64 0) (Z_to_bv 64 1) mt j56 (Z_to_bv 64 (nthP P1 P2 P3 na)) j72) ->
    (exists scs, rw_cells rsegs m (q + -368) [CB 256 scs]) ->
    rw_cells rsegs m (q + -112) (vhi canary ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) ->
    stk rsegs m (q - VF_DEPTH) (q + -480) -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
    (exists ev : word, rw_cells rsegs m ERRNOA [C4 ev]) ->
    rw_cells rsegs m AP [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w] ->
    (exists (v1 v2 : word) (v3 : list byte), rw_cells rsegs m P1 [C4 v1] /\ rw_cells rsegs m P2 [C4 v2] /\ rw_cells rsegs m P3 [CB w3n v3]) ->
    bytes_at rsegs m FA (zbytes fmtl) ->
    rw_cells rsegs m Fp (rf_cells T co f ssJ) -> RFJ' co k c f -> (0 <= k)%Z -> sh_stdio f = true ->
    fmt_enc (skipn (Z.to_nat (i + 2)) fmtl) ds' -> (0 <= i)%Z ->
    (0 <= mt <= na)%Z -> (na + 1 + nconv ds' <= W3num)%Z ->
    (sh_cnt f = 0%Z -> r = mt) -> (sh_cnt f <> 0%Z -> vfs fuel ds' f (mt + 1) = Some r) ->
    evt rsegs (POST r)
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 (FA + i + 1)) xw x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 0) (Z_to_bv 64 100) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (nthP P1 P2 P3 na)) (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x206f0) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. exact (@F_vfscanf_D1.L_65c ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3). Qed.

  Lemma L_3c0 : forall ds', LH ds' ->
    forall m (i : Z) f co k c (mt na : Z) r f6 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x27 x28 x29 x30 x31 : word) j16 j56 j72,
    mem_inv rsegs m -> munch (vf_FP q P1 P2 P3) m0 m -> wmono rsegs m0 m ->
    rw_cells rsegs m (q + -480) (vlow (Z_to_bv 64 (AP + 8 * (na + 1))) j16 (Z_to_bv 64 0) (Z_to_bv 64 1) mt j56 (Z_to_bv 64 (nthP P1 P2 P3 na)) j72) ->
    (exists scs, rw_cells rsegs m (q + -368) [CB 256 scs]) ->
    rw_cells rsegs m (q + -112) (vhi canary ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) ->
    stk rsegs m (q - VF_DEPTH) (q + -480) -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
    (exists ev : word, rw_cells rsegs m ERRNOA [C4 ev]) ->
    rw_cells rsegs m AP [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w] ->
    (exists (v1 v2 : word) (v3 : list byte), rw_cells rsegs m P1 [C4 v1] /\ rw_cells rsegs m P2 [C4 v2] /\ rw_cells rsegs m P3 [CB w3n v3]) ->
    bytes_at rsegs m FA (zbytes fmtl) ->
    rw_cells rsegs m Fp (rf_cells T co f ssJ) -> RFJ' co k c f -> (1 <= k)%Z -> c <> 0%Z -> sh_stdio f = true ->
    fmt_enc (skipn (Z.to_nat (i + 2)) fmtl) ds' -> (0 <= i)%Z ->
    (0 <= mt <= na)%Z -> (na + 1 + nconv ds' <= W3num)%Z ->
    intscan fuel 10 0 (sh_unget f) = Some f6 ->
    (sh_cnt f6 = 0%Z -> r = mt) -> (sh_cnt f6 <> 0%Z -> vfs fuel ds' f6 (mt + 1) = Some r) ->
    evt rsegs (POST r)
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 (FA + i + 1)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 0) (Z_to_bv 64 100) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (nthP P1 P2 P3 na)) (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x20454) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. pose proof ctx_all as Hctx_all.
    intros ds' HLH. intros until j72. intros MI MU WM LOW [scs SCS] HI ST BY [SSP1 SSP2] [ev ERR] APC (v1 & v2 & v3 & PC1 & PC2 & PC3) FMB FC RJ Hk Hcnz Hst FE Hi Hmt Hna HM HV0 HV1. hush.
    pose proof (nconv_nonneg ds') as NCV.
    unfold vlow, got_ssp, ssp_guard in LOW. unfold vhi in HI. unfold vf_FP, ERRNOA, VF_DEPTH in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
    site_facts FC RJ co k c f.
    pose proof (zbytes_length txt) as LTX. pose proof (zbytes_length fmtl) as LTF. unfold zlength in *. pose_word_ranges.
    pose proof (RFI_unget T txt p ssJ Hp2 co k c f RJ Hk) as RJu.

    assert (CALL : forall m1 fcells, mem_inv rsegs m1 -> munch [((q - 720)%Z, q); (Fp, (Fp + 232)%Z); (P1, (P1 + 4)%Z); (P2, (P2 + 4)%Z); (P3, (P3 + 4)%Z); (243580%Z, (243580 + 4)%Z)] m0 m1 -> wmono rsegs m0 m1 ->
      rw_cells rsegs m1 (q + -480) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 375432); C8 j16; C8 (Z_to_bv 64 (AP + 8 * (na + 1))%Z); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 mt); C8 j56; C8 (Z_to_bv 64 (nthP P1 P2 P3 na)); CB 40 j72] ->
      rw_cells rsegs m1 (q + -368) [CB 256 scs] ->
      rw_cells rsegs m1 (q + -112) [C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
      stk rsegs m1 (q - 720)%Z (q + -480)%Z -> bytes_at rsegs m1 T (zbytes txt) ->
      rw_cells rsegs m1 172368 [C8 (Z_to_bv 64 375432)] -> rw_cells rsegs m1 375432 [C8 canary] -> rw_cells rsegs m1 243580 [C4 ev] ->
      rw_cells rsegs m1 AP [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w] ->
      rw_cells rsegs m1 P1 [C4 v1] -> rw_cells rsegs m1 P2 [C4 v2] -> rw_cells rsegs m1 P3 [CB w3n v3] -> bytes_at rsegs m1 FA (zbytes fmtl) ->
      rw_cells rsegs m1 Fp fcells -> fcells = rf_cells T co (sh_unget f) ssJ ->
      forall x10',
      evt rsegs (POST r)
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 (FA + i + 1)) x10' x11 x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 0) (Z_to_bv 64 100) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (nthP P1 P2 P3 na)) (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x20468) fc None m1 (seg_rom rsegs))).
    { clear MI MU WM LOW SCS HI ST BY SSP1 SSP2 ERR APC PC1 PC2 PC3 FMB FC BFC.
      intros m1 fcells MI MU WM LOW SCS HI ST BY SSP1 SSP2 ERR APC PC1 PC2 PC3 FMB FC -> x10'.
      pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
      zs. zs. zs. br K1. zs. zs. zs. zs. zs. zs. zs. zs.
      zs. zs.
      zs. zs. zs.
      pose proof intscan_spec as IS. unfold intscan_stmt, intscan_post, is_W, IS_DEPTH, INTSCAN, got_ssp, ssp_guard in IS.
      replace 243580%Z with (bv_unsigned tp - 164)%Z in ERR by lia.
      replace 243580%Z with (bv_unsigned tp - 164)%Z in MU by lia.
      zs. let v := getreg 13%Z in replace v with (Z_to_bv 64 18446744073709551615) by (apply Z_to_bv_eqm; reflexivity).
      callw (eapply IS with (pre := pre) (post := post) (p := p) (txt := txt) (fuel := fuel) (base := 10%Z) (pok := 0%Z);
        [ exact HM | intros _; split; [exact TXT | exact Hp] | exact BYT | pose proof Hp2; unfold zlength in *; lia | exact Hnul | exact FC | exact RJu | lia | exact Hcnz | split; reflexivity
        | exact BY | split; [exact SSP1 | exact SSP2] | exact ERR | lia | lia | unfold zlength; lia1f
        | replace (q + -480 - 240)%Z with (q - 720)%Z by lia; exact ST | lia | lia | lia | lia | unfold zlength; lia1f | lia | unfold zlength; lia1f | unfold zlength; lia1f | lia
        | lia | lia | unfold zlength; lia1f | lia | lia | lia | lia | lia | exact MI ]).
      clear IS.
      match goal with H : RFJ _ _ _ _ ?co' ?k' ?c' f6 |- _ => rename H into RJ6 end.
      match goal with H : rw_cells _ ?m' Fp (rf_cells _ _ f6 _) |- _ => rename H into FC6 end.
      match goal with H : ssp_cells ?m' _ |- _ => destruct H as [SSP1' SSP2'] end.
      match goal with H : rw_cells _ ?m' (bv_unsigned tp - 164)%Z _ |- _ => replace (bv_unsigned tp - 164)%Z with 243580%Z in H by lia; rename H into ERR6 end.
      match goal with H : munch _ m0 ?m' |- _ => replace (bv_unsigned tp - 164)%Z with 243580%Z in H by lia end.
      match goal with H : stk _ ?m' (q + -480 - 240)%Z _ |- _ => replace (q + -480 - 240)%Z with (q - 720)%Z in H by lia; rename H into ST6 end.
      eapply (L_65c ds' HLH) with (k := 0%Z); try eassumption.
      all: try (eexists; eassumption); try (split; assumption); try (do 3 eexists; split; [eassumption | split; eassumption]); try lia.
      { eapply RFJ_k0. exact RJ6. }
      rewrite (intscan_stdio _ _ _ _ _ HM), stdio_unget. exact Hst. }
    unfold_fc2 FC.
    destruct (sh_shlim_neg f) eqn:SN.
    - rewrite (rf_unget_nop f SN) in *. zs. zs. br K0.
      eapply (CALL _ (rf_cells T co f ssJ)); try eassumption; try reflexivity. unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; fc_goal2.
    - rewrite (rf_unget_eq f SN) in *. zs. zs. br K0. zs. zs. zs.
      eapply (CALL _ (rf_cells T co (mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) ssJ)); try eassumption; try reflexivity.
      unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; fc_goal2.
  Qed.

  Lemma L_39c : forall ds', LH ds' ->
    forall m (i : Z) f co k c (mt na : Z) r (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x27 x28 x29 x30 x31 : word) j16 j56 j72,
    mem_inv rsegs m -> munch (vf_FP q P1 P2 P3) m0 m -> wmono rsegs m0 m ->
    rw_cells rsegs m (q + -480) (vlow (Z_to_bv 64 (AP + 8 * (na + 1))) j16 (Z_to_bv 64 0) (Z_to_bv 64 1) mt j56 (Z_to_bv 64 (nthP P1 P2 P3 na)) j72) ->
    (exists scs, rw_cells rsegs m (q + -368) [CB 256 scs]) ->
    rw_cells rsegs m (q + -112) (vhi canary ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) ->
    stk rsegs m (q - VF_DEPTH) (q + -480) -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
    (exists ev : word, rw_cells rsegs m ERRNOA [C4 ev]) ->
    rw_cells rsegs m AP [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w] ->
    (exists (v1 v2 : word) (v3 : list byte), rw_cells rsegs m P1 [C4 v1] /\ rw_cells rsegs m P2 [C4 v2] /\ rw_cells rsegs m P3 [CB w3n v3]) ->
    bytes_at rsegs m FA (zbytes fmtl) ->
    rw_cells rsegs m Fp (rf_cells T co f ssJ) -> RFJ' co k c f -> (0 <= k)%Z -> c <> 0%Z -> sh_stdio f = true ->
    fmt_enc (skipn (Z.to_nat (i + 2)) fmtl) ds' -> (0 <= i)%Z ->
    (0 <= mt <= na)%Z -> (na + 1 + nconv ds' <= W3num)%Z ->
    (let '(c4, f4) := sh_getc f in
     if (c4 <? 0)%Z then r = (if mt =? 0 then -1 else mt)%Z
     else exists f6, intscan fuel 10 0 (sh_unget f4) = Some f6 /\ (sh_cnt f6 = 0%Z -> r = mt) /\ (sh_cnt f6 <> 0%Z -> vfs fuel ds' f6 (mt + 1) = Some r)) ->
    evt rsegs (POST r)
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 (FA + i + 1)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 0) (Z_to_bv 64 100) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (nthP P1 P2 P3 na)) (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x20430) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. pose proof ctx_all as Hctx_all.
    intros ds' HLH. intros until j72. intros MI MU WM LOW [scs SCS] HI ST BY [SSP1 SSP2] [ev ERR] APC (v1 & v2 & v3 & PC1 & PC2 & PC3) FMB FC RJ Hk Hcnz Hst FE Hi Hmt Hna HV. hush.
    pose proof (nconv_nonneg ds') as NCV.
    pose proof LOW as LOW'. unfold vlow, got_ssp, ssp_guard in LOW. unfold vhi in HI. unfold vf_FP, ERRNOA, VF_DEPTH in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
    site_facts FC RJ co k c f.
    pose proof (zbytes_length txt) as LTX. pose proof (zbytes_length fmtl) as LTF. unfold zlength in *. pose_word_ranges.
    pose proof (getc_nz co k c f RJ Hst) as NZ1. pose proof (stdio_getc f) as Hst1. rewrite Hst in Hst1.
    rewrite (surjective_pairing (sh_getc f)) in HV.
    destruct (Z.eq_dec (T + sh_rpos f) (rf_rend T co f)) as [SLOW|FAST].
    -
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. br K.
      destruct (rf_getc_slow T txt p ssJ Hp2 T1 co k c f RJ SLOW) as (STD & EJ & Hn & Hrp & Hco & Hlat & Hc0').
      pose proof (RFI_getc_slow T txt p ssJ BYT Hp2 T1 co k c f RJ SLOW) as RJ1.
      destruct (stk_split _ _ _ (q + -480 - 160)%Z _ ST ltac:(lia)) as [STlo SThi]. clear ST.
      zs. zs. callw (eapply shgetc_callJ;
        [ exact FC0 | exact RJ | exact SLOW | exact TXT | exact Hp | exact BY | exact (conj SSP1 SSP2)
        | plia | plia | plia | exact SThi | plia | plia | plia | plia | plia | plia | plia | plia | plia | hyp ]).
      post_getc. rename SSP1' into SSP1. rename SSP2' into SSP2. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC2 end.
      match goal with H : stk _ ?m' (q + -480 - 160)%Z _ |- _ => pose proof (stk_merge _ _ _ _ _ STlo H ltac:(lia)) as ST; clear STlo H end.
      assert (Rc1 : (-1 <= fst (sh_getc f) < 256)%Z) by (destruct RJ1 as (_ & R & _); lia).
      zs. brf K1.
      +
        replace (fst (sh_getc f) <? 0)%Z with true in HV by (symmetry; apply Z.ltb_lt; mlia2). rewrite HV.
        eapply L_9c8; try eassumption. { split; assumption. } lia.
      + replace (fst (sh_getc f) <? 0)%Z with false in HV by (symmetry; apply Z.ltb_ge; mlia2).
        destruct HV as (f6 & HM & HV0 & HV1).
        eapply (L_3c0 ds' HLH); try eassumption.
        all: try (eexists; eassumption); try (split; assumption); try (do 3 eexists; split; [eassumption | split; eassumption]); try lia.
    -
      pose proof (RFI_getc T txt p ssJ BYT Hp2 Hnul co k c f RJ Hcnz FAST) as RJ1.
      pose proof (rf_getc_fast_lt T txt p ssJ Hp2 co k c f RJ Hcnz FAST) as LT.
      pose proof (rf_getc_fast T txt p ssJ Hp2 co k c f RJ FAST) as EG.
      rewrite EG in RJ1, HV, NZ1, Hst1. cbn [fst snd] in RJ1, HV, NZ1, Hst1.
      pose proof (proj1 (Forall_forall _ _) BYT (znth txt (sh_rpos f)) ltac:(apply znth_In; unfold zlength in *; lia)) as Rchr. cbv beta in Rchr.
      replace (znth txt (sh_rpos f) <? 0)%Z with false in HV by (symmetry; apply Z.ltb_ge; lia).
      destruct HV as (f6 & HM & HV0 & HV1).
      unfold_fc2 FC.
      zs. zs. zs. br K. zs. zs. zs.
      eapply (L_3c0 ds' HLH); try eassumption.
      all: try (eexists; eassumption); try (split; assumption); try (do 3 eexists; split; [eassumption | split; eassumption]); try lia.
      fc_goal2.
  Qed.

  Lemma L_368 : forall ds', LH ds' ->
    forall m (i : Z) f co k c (mt na : Z) r (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x27 x28 x29 x30 x31 : word) j16 j56 j72,
    mem_inv rsegs m -> munch (vf_FP q P1 P2 P3) m0 m -> wmono rsegs m0 m ->
    rw_cells rsegs m (q + -480) (vlow (Z_to_bv 64 (AP + 8 * (na + 1))) j16 (Z_to_bv 64 0) (Z_to_bv 64 1) mt j56 (Z_to_bv 64 (nthP P1 P2 P3 na)) j72) ->
    (exists scs, rw_cells rsegs m (q + -368) [CB 256 scs]) ->
    rw_cells rsegs m (q + -112) (vhi canary ra s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e) ->
    stk rsegs m (q - VF_DEPTH) (q + -480) -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
    (exists ev : word, rw_cells rsegs m ERRNOA [C4 ev]) ->
    rw_cells rsegs m AP [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w] ->
    (exists (v1 v2 : word) (v3 : list byte), rw_cells rsegs m P1 [C4 v1] /\ rw_cells rsegs m P2 [C4 v2] /\ rw_cells rsegs m P3 [CB w3n v3]) ->
    bytes_at rsegs m FA (zbytes fmtl) ->
    rw_cells rsegs m Fp (rf_cells T co f ssJ) -> RFJ' co k c f -> (1 <= k)%Z -> c <> 0%Z -> sh_stdio f = true ->
    fmt_enc (skipn (Z.to_nat (i + 2)) fmtl) ds' -> (0 <= i)%Z ->
    (0 <= mt <= na)%Z -> (na + 1 + nconv ds' <= W3num)%Z ->
    (let '(c4, f4) := sh_getc (sh_lim0 (sh_unget f)) in
     if (c4 <? 0)%Z then r = (if mt =? 0 then -1 else mt)%Z
     else exists f6, intscan fuel 10 0 (sh_unget f4) = Some f6 /\ (sh_cnt f6 = 0%Z -> r = mt) /\ (sh_cnt f6 <> 0%Z -> vfs fuel ds' f6 (mt + 1) = Some r)) ->
    evt rsegs (POST r)
      (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 (FA + i + 1)) x10 x11 x12 x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 0) (Z_to_bv 64 100) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (nthP P1 P2 P3 na)) (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x203fc) fc None m (seg_rom rsegs)).
  Proof using ra q gp tp s0e s1e s2e s3e s4e s5e s6e s7e s8e s9e s10e s11e F fc m0 T p txt pre post canary P1 P2 P3 FA fmtl fuel W3num w3n ap3w TXT Hp Hfuel T0 TW T1 SPLO Q1 TPV SPT HP1 HP2 HP3 HP1q HP2q HP3q HP1t HP2t HP3t HP12 HP13 HP23 HFA FMR HW3 HAP3 HP3q3. try hush. pose proof ctx_all as Hctx_all.
    intros ds' HLH. intros until j72. intros MI MU WM LOW [scs SCS] HI ST BY [SSP1 SSP2] [ev ERR] APC (v1 & v2 & v3 & PC1 & PC2 & PC3) FMB FC RJ Hk Hcnz Hst FE Hi Hmt Hna HV. hush.
    pose proof (nconv_nonneg ds') as NCV.
    unfold vlow, got_ssp, ssp_guard in LOW. unfold vhi in HI. unfold vf_FP, ERRNOA, VF_DEPTH in *. unfold got_ssp, ssp_guard in SSP1, SSP2.
    site_facts FC RJ co k c f.
    pose proof (zbytes_length txt) as LTX. pose proof (zbytes_length fmtl) as LTF. unfold zlength in *. pose_word_ranges.
    pose proof (RFI_unget T txt p ssJ Hp2 co k c f RJ Hk) as RJu.
    pose proof (RFI_lim0 T txt p ssJ Hp2 co (k - 1) c (sh_unget f) RJu) as RJl.

    assert (TAIL : forall m1 fcells, mem_inv rsegs m1 -> munch [((q - 720)%Z, q); (Fp, (Fp + 232)%Z); (P1, (P1 + 4)%Z); (P2, (P2 + 4)%Z); (P3, (P3 + 4)%Z); (243580%Z, (243580 + 4)%Z)] m0 m1 -> wmono rsegs m0 m1 ->
      rw_cells rsegs m1 (q + -480) [C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 375432); C8 j16; C8 (Z_to_bv 64 (AP + 8 * (na + 1))%Z); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 1); C8 (Z_to_bv 64 mt); C8 j56; C8 (Z_to_bv 64 (nthP P1 P2 P3 na)); CB 40 j72] ->
      rw_cells rsegs m1 (q + -368) [CB 256 scs] ->
      rw_cells rsegs m1 (q + -112) [C8 canary; C8 s11e; C8 s10e; C8 s9e; C8 s8e; C8 s7e; C8 s6e; C8 s5e; C8 s4e; C8 s3e; C8 s2e; C8 s1e; C8 s0e; C8 ra] ->
      stk rsegs m1 (q - 720)%Z (q + -480)%Z -> bytes_at rsegs m1 T (zbytes txt) ->
      rw_cells rsegs m1 172368 [C8 (Z_to_bv 64 375432)] -> rw_cells rsegs m1 375432 [C8 canary] -> rw_cells rsegs m1 243580 [C4 ev] ->
      rw_cells rsegs m1 AP [C8 (Z_to_bv 64 P1); C8 (Z_to_bv 64 P2); C8 ap3w] ->
      rw_cells rsegs m1 P1 [C4 v1] -> rw_cells rsegs m1 P2 [C4 v2] -> rw_cells rsegs m1 P3 [CB w3n v3] -> bytes_at rsegs m1 FA (zbytes fmtl) ->
      rw_cells rsegs m1 Fp fcells -> fcells = rf_cells T co (sh_unget f) ssJ ->
      forall x10' x11',
      evt rsegs (POST r)
        (MS (mkR x1 SPv gp tp x5 x6 x7 (Z_to_bv 64 Fp) (Z_to_bv 64 (FA + i + 1)) x10' x11' x12 x13 x14 x15 x16 x17
                 x18 (Z_to_bv 64 0) (Z_to_bv 64 100) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 (nthP P1 P2 P3 na)) (Z_to_bv 64 32) (Z_to_bv 64 5) (Z_to_bv 64 10) x27 x28 x29 x30 x31)
            F (Z_to_bv 64 0x20410) fc None m1 (seg_rom rsegs))).
    { clear MI MU WM LOW SCS HI ST BY SSP1 SSP2 ERR APC PC1 PC2 PC3 FMB FC BFC.
      intros m1 fcells MI MU WM LOW SCS HI ST BY SSP1 SSP2 ERR APC PC1 PC2 PC3 FMB FC -> x10' x11'.
      pose proof (rw_cells_bound _ _ _ _ FC) as BFC. cbn [cells_size csize Nat.add rf_cells] in BFC.
      pose proof FC as FC0. unfold_fc2 FC.
      zs. zs. zs. zs. zs.
      rewrite rf_cells_raw_eq in FC0.
      pose proof shlim_spec as SL. unfold shlim_stmt in SL.
      zs. zs. zs. callw (eapply SL with (txt := txt); [exact FC0 | exact (RFI_ok T txt p ssJ co (k - 1) c _ RJu) | reflexivity | reflexivity | lia | lia | | exact MI];
                              intros STD; pose proof Hp2; destruct RJu as ((_ & _ & Rru & _) & _ & _ & _ & _ & SSu); destruct (SSu STD) as (X1 & X2 & X3); unfold zlength in *; lia).
      clear SL. match goal with H : rw_cells _ ?m' Fp _ |- _ => rename H into FC1 end.
      eapply (L_39c ds' HLH) with (k := 0%Z); try eassumption.
      all: try (eexists; eassumption); try (split; assumption); try (do 3 eexists; split; [eassumption | split; eassumption]); try lia.
      rewrite stdio_lim0, stdio_unget; exact Hst. }
    unfold_fc2 FC.
    destruct (sh_shlim_neg f) eqn:SN.
    - rewrite (rf_unget_nop f SN) in *. zs. zs. zs. br K0.
      eapply (TAIL _ (rf_cells T co f ssJ)); try eassumption; try reflexivity. unfold rf_cells; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; fc_goal2.
    - rewrite (rf_unget_eq f SN) in *. zs. zs. zs. br K0. zs. zs.
      eapply (TAIL _ (rf_cells T co (mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)) ssJ)); try eassumption; try reflexivity.
      unfold rf_cells, rf_rend; cbn [sh_stdio sh_n sh_buf sh_rpos sh_cnt0 sh_shlim_neg]; rewrite ?SN; fc_goal2.
  Qed.

End Vfscanf.
