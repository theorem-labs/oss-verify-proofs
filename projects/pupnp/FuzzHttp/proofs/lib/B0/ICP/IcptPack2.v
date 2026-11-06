(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac ZBridge STRW_tac Image Arr Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts Globals IcptA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import CellConv.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ICP Require Import IcptKit M_sspdefs M_stdio_base N_ictx N_stkhi N_shgetc_B N_vfscanf_lib N_vfscanf_pure I_sscanf I_scanf_common.
Import ListNotations.
Open Scope Z_scope.

Section P.
Context {HC : HasCeiling}.

#[using="Type"] Lemma rtext_facts : forall T txt pre post, rtext_A T txt pre post ->
  0 <= zlength pre < zlength txt /\ znth txt (zlength pre) = 0 /\ (forall i, 0 <= i < zlength pre -> znth txt i <> 0) /\ Forall (fun c => 0 <= c < 256) txt.
Proof.
  intros T txt pre post (Htxt & NZ & BYT & AL & L40).
  split; [rewrite Htxt; unfold zlength; rewrite length_app; cbn [length]; lia|].
  split; [rewrite Htxt; rewrite znth_app_r by (unfold zlength; lia); rewrite Z.sub_diag; reflexivity|].
  split; [| exact BYT].
  intros i Hi. rewrite Htxt. rewrite znth_app_l by exact Hi. pose proof (proj1 (Forall_forall _ _) NZ (znth pre i) (znth_In pre i Hi)) as X. cbv beta in X. lia.
Qed.

#[using="Type"] Lemma ic_sscanf_status_proof : sscanf_status_stmt_A.
Proof.
  intros until lox. intros TXT BY ACT RDT WT NT ACF RDF AC1 RD1 W1 AC2 RD2 W2 AC3 RD3 W3 ST MI AE CLO LO Q16 Q64 Q47 ACS RDS TPV T0 THI HP1 HP2 HP3 HP1t HP2t HP3t HP12 HP13 HP23 GOT GUARD ERR PC1 PC2 PC3.
  intros -> -> -> -> ->.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_SSCANF_DEPTH in LO.
  destruct (rtext_facts _ _ _ _ TXT) as (Hp & Hnul & Hpre & BYT).
  destruct (sscanf_model_total txt (zlength pre) Hp Hnul Hpre BYT FMT_STATUSLINE) as (r & HV & HR).
  assert (TPU : bv_unsigned tpx = 6190512) by (rewrite TPV; apply unsigned_lit; lia).
  assert (L40 : zlength txt <= 2^40) by (destruct TXT as (_ & _ & _ & _ & L); exact L).
  assert (IW : iwin T (zlength pre) lox qx tpx).
  { unfold iwin. destruct WT as [Hn WTT]. unfold cwin. rewrite TPU. unfold zlength in *. repeat split; lia. }
  assert (SHW : shw_ok (ssi_W P1 P2 P3 qx)).
  { unfold shw_ok, ssi_W, SSI_DEPTH, ERRNOA. destruct W1 as [_ W1']. destruct W2 as [_ W2']. destruct W3 as [_ W3'].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }
  destruct (stk_split _ _ _ (qx - 3408) _ ST ltac:(lia)) as [STlo SThi].
  eapply evt_mono.
  { eapply sscanf_i_spec with (T := T) (p := zlength pre) (txt := txt) (pre := pre) (post := post) (canary := canary) (P1 := P1) (P2 := P2) (P3 := P3)
      (lox := lox) (qx := qx) (FA := A0_FMT) (FN := 11) (fmtl := FMTL_STATUS) (fmtd := FMT_STATUSLINE) (ds' := [SW; SL 46; SW; SD; SW; SD])
      (W3num := 3) (w3n := 4%nat) (q := qx) (r := r) (ev := ev) (v1 := v1) (v2 := v2) (v3 := v3);
      first [ exact scanf_common_spec | exact fmt_at | exact fmt_enc_status | exact TXT | exact IW | exact TPU | exact W1 | exact W2 | exact W3
            | exact HV | exact MI | exact PC1 | exact PC2 | exact PC3 | exact BY | exact ERR | exact SThi | reflexivity
            | split; [exact GOT| exact GUARD]
            | right; split; reflexivity | intros _; reflexivity
            | unfold FMTL_STATUS; repeat (apply Forall_cons; [lia|]); apply Forall_nil
            | unfold psep; repeat split; assumption
            | exact (conj IE (conj ACT (conj RDT (conj ACS RDS))))
            | unfold pctx; repeat split; assumption
            | unfold cwin, A0_FMT; lia
            | cbn [nconv FMT_STATUSLINE]; lia
            | unfold A0_FMT, FMTL_STATUS, zlength; cbn [length]; lia
            | unfold SSI_DEPTH, zlength in *; lia ]. }
  intros ms' Q. unfold ssi_post in Q. unfold sscanf3_post_A.
  destruct Q as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & ev' & w1 & w2 & w3 & E & MU & WM & MI' & ST' & BY' & [G' U'] & ERR' & PA & PB & PC).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', ev', w1, w2, w3, r.
  assert (CWS : cwin lox (qx - lox)) by (unfold cwin; lia).
  unfold SSI_DEPTH in ST'.
  split; [exact E|].
  split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, ssi_W, SSI_DEPTH, ERRNOA, A0_ERRNO. cbn [outside]. intros x (O1 & O2 & O3 & O4 & O5 & _). repeat split; try assumption; lia. }
  split; [exact WM|]. split; [exact MI'|].
  split. { eapply stk_merge; [| exact ST' | lia].
           eapply stk_transport_disjoint; [exact STlo | exact MU | exact WM |]. unfold ssi_W, SSI_DEPTH, ERRNOA. cbn [disjoint_from]. repeat split; try lia; exact I. }
  split. { eapply asan_env_frame; [exact AE | exact MU | exact WM |]. unfold ssi_W, SSI_DEPTH, ERRNOA, env_safe.
           apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia|].
           apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]. }
  split. { eapply accessible_munch; [exact ACS | exact MU | exact CWS | intros s Hs; apply (shw_outside _ s SHW); lia]. }
  split. { eapply sh_readable_munch; [exact RDS | exact MU | exact CWS | intros s Hs; apply (shw_outside _ s SHW); lia]. }
  split; [exact HV|]. split; [cbn [nconv FMT_STATUSLINE] in HR; lia|].
  split; [exact G'|]. split; [exact U'|]. split; [exact ERR'|]. split; [exact PA|]. split; [exact PB| exact PC].
Qed.

#[using="Type"] Lemma ic_sscanf_version_proof : sscanf_version_stmt_A.
Proof.
  intros until lox. intros TXT BY ACT RDT WT NT ACF RDF AC1 RD1 W1 AC2 RD2 W2 ST MI AE CLO LO Q16 Q64 Q47 ACS RDS TPV T0 THI HP1 HP2 HP1t HP2t HP12 GOT GUARD ERR PC1 PC2.
  intros -> -> -> ->.
  pose proof alloc_ceiling_bounds as ACB. pose proof (icpt_env_of_asan_env _ AE) as IE. unfold A0_SSCANF_DEPTH in LO.
  destruct (rtext_facts _ _ _ _ TXT) as (Hp & Hnul & Hpre & BYT).
  destruct (sscanf_model_total txt (zlength pre) Hp Hnul Hpre BYT FMT_VERSION) as (r & HV & HR).
  assert (TPU : bv_unsigned tpx = 6190512) by (rewrite TPV; apply unsigned_lit; lia).
  assert (L40 : zlength txt <= 2^40) by (destruct TXT as (_ & _ & _ & _ & L); exact L).
  assert (IW : iwin T (zlength pre) (lox + 4) qx tpx).
  { unfold iwin. destruct WT as [Hn WTT]. unfold cwin. rewrite TPU. unfold zlength in *. repeat split; lia. }
  assert (W3 : cwin lox 4) by (unfold cwin; lia).
  assert (SHW : shw_ok (ssi_W P1 P2 lox qx)).
  { unfold shw_ok, ssi_W, SSI_DEPTH, ERRNOA. destruct W1 as [_ W1']. destruct W2 as [_ W2'].
    repeat (apply Forall_cons; [cbn [fst snd]; lia|]). apply Forall_nil. }

  destruct (stk_split _ _ _ (qx - 3408) _ ST ltac:(lia)) as [STlo SThi].
  destruct (stk_split _ _ _ (lox + 4) _ STlo ltac:(lia)) as [ST4 STmid]. clear STlo.
  destruct (stk_carve asegs m lox (lox + Z.of_nat 4) 4 ltac:(replace (lox + Z.of_nat 4) with (lox + 4) by lia; exact ST4) ltac:(lia)) as [_ [j4 PC3]].
  replace (lox + Z.of_nat 4 - Z.of_nat 4) with lox in PC3 by lia.
  apply (rw_cells_CB_C4 asegs m lox [] j4 []) in PC3. cbn [app] in PC3.
  eapply evt_mono.
  { eapply sscanf_i_spec with (T := T) (p := zlength pre) (txt := txt) (pre := pre) (post := post) (canary := canary) (P1 := P1) (P2 := P2) (P3 := lox)
      (lox := (lox + 4)%Z) (qx := qx) (FA := A0_FMT2) (FN := 8) (fmtl := FMTL_VERSION) (fmtd := FMT_VERSION) (ds' := [SW; SL 46; SW; SD])
      (W3num := 2) (w3n := 0%nat) (q := qx) (r := r) (ev := ev) (v1 := v1) (v2 := v2) (v3 := le_bytes_to_word j4);
      first [ exact scanf_common2_spec | exact fmt2_at | exact fmt_enc_version | exact TXT | exact IW | exact TPU | exact W1 | exact W2 | exact W3
            | exact HV | exact MI | exact PC1 | exact PC2 | exact PC3 | exact BY | exact ERR | exact SThi | reflexivity
            | split; [exact GOT| exact GUARD]
            | left; split; reflexivity | intros X; exfalso; clear - X; lia
            | unfold FMTL_VERSION; repeat (apply Forall_cons; [lia|]); apply Forall_nil
            | unfold psep; unfold zlength in *; repeat split; first [assumption | lia]
            | refine (conj IE (conj ACT (conj RDT (conj _ _)))); [eapply accessible_sub; [exact ACS| lia| lia] | eapply sh_readable_sub; [exact RDS| lia| lia| lia]]
            | unfold pctx; repeat split; first [ assumption | eapply accessible_sub; [exact ACS| lia| lia] | eapply sh_readable_sub; [exact RDS| lia| lia| lia] ]
            | unfold cwin, A0_FMT2; lia
            | cbn [nconv FMT_VERSION]; lia
            | unfold A0_FMT2, FMTL_VERSION, zlength; cbn [length]; lia
            | unfold SSI_DEPTH, zlength in *; lia ]. }
  intros ms' Q. unfold ssi_post in Q. unfold sscanf2_post_A.
  destruct Q as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & ev' & w1 & w2 & w3 & E & MU & WM & MI' & ST' & BY' & [G' U'] & ERR' & PA & PB & PC).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m', ev', w1, w2, r.
  assert (CWS : cwin lox (qx - lox)) by (unfold cwin; lia).
  unfold SSI_DEPTH in ST'.
  split; [exact E|].
  split. { eapply munch_weaken; [| exact MU]. unfold sub_fp, ssi_W, SSI_DEPTH, ERRNOA, A0_ERRNO. cbn [outside]. intros x (O1 & O2 & O3 & O4 & _). repeat split; try assumption; lia. }
  split; [exact WM|]. split; [exact MI'|].
  split. { pose proof (stk_of_rw_cells asegs _ _ _ PC) as S4. cbn [cells_size csize Nat.add] in S4. replace (lox + Z.of_nat 4) with (lox + 4) in S4 by lia.
           assert (SM : stk asegs m' (lox + 4) (qx - 3408)).
           { eapply stk_transport_disjoint; [exact STmid | exact MU | exact WM |]. unfold ssi_W, SSI_DEPTH, ERRNOA. cbn [disjoint_from]. repeat split; try lia; exact I. }
           eapply stk_merge; [| exact ST' | lia]. eapply stk_merge; [exact S4 | exact SM | lia]. }
  split. { eapply asan_env_frame; [exact AE | exact MU | exact WM |]. unfold ssi_W, SSI_DEPTH, ERRNOA, env_safe.
           apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [left; cbn [fst snd]; lia|].
           apply Forall_cons; [left; cbn [fst snd]; lia|]. apply Forall_cons; [cbn [fst snd]; lia| apply Forall_nil]. }
  split. { eapply accessible_munch; [exact ACS | exact MU | exact CWS | intros s Hs; apply (shw_outside _ s SHW); lia]. }
  split. { eapply sh_readable_munch; [exact RDS | exact MU | exact CWS | intros s Hs; apply (shw_outside _ s SHW); lia]. }
  split; [exact HV|]. split; [cbn [nconv FMT_VERSION] in HR; lia|].
  split; [exact G'|]. split; [exact U'|]. split; [exact ERR'|]. split; [exact PA| exact PB].
Qed.
End P.
