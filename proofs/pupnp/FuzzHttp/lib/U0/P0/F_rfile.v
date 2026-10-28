(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFModel Arr.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim StrFun ScanInt.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.Lib Require Import SFW1_lemmas.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Import Segs F_memcpy F_memchr Printf_lib.
From OssFuzzTheorems.Proofs.pupnp.FuzzHttp.lib.U0.P0 Require Export F_shgetc.
Import ListNotations.
Open Scope Z_scope.

Definition RFJ (T : Z) (txt : list Z) (p : Z) (J : rfj) (co kmin c : Z) (f : shfile) : Prop :=
  sh_ok T txt f /\ (-1 <= c < 256)%Z /\ (0 <= sh_cnt0 f <= sh_rpos f)%Z /\
  (sh_shlim_neg f = false -> sh_cnt0 f + kmin <= sh_rpos f)%Z /\
  (sh_stdio f = false -> sh_shlim_neg f = false /\ sh_rpos f <= p + 1 /\ (c <> 0%Z -> sh_rpos f <= p))%Z /\
  (sh_stdio f = true -> sh_n f = p /\ sh_rpos f <= co <= p /\ (sh_shlim_neg f = true -> sh_rpos f = p) /\ J = ssJ)%Z.

Section RF.
  Variables (T : Z) (txt : list Z) (p : Z) (J : rfj).
  Hypothesis BYT : Forall (fun c => 0 <= c < 256) txt.
  Hypothesis Hp : 0 <= p < zlength txt.
  Hypothesis Hnul : znth txt p = 0.
  Hypothesis T0 : 4096 <= T.
  Hypothesis T1 : T + 2^41 <= 2^63.

  Notation RFI := (RFJ T txt p J).

  #[using="Type"] Lemma RFI_ok : forall co kmin c f, RFI co kmin c f -> sh_ok T txt f.
  Proof. intros co kmin c f (OK & _). exact OK. Qed.

  #[using="Hp"] Lemma RFI_rpos : forall co kmin c f, RFI co kmin c f -> 0 <= sh_rpos f <= p + 1.
  Proof.
    intros co kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    destruct (sh_stdio f) eqn:ES; [destruct (SS eq_refl) as (N1 & N2 & _); lia | destruct (NS eq_refl) as (N1 & N2 & N3); lia].
  Qed.

  #[using="Hp"] Lemma rf_getc_fast : forall co kmin c f, RFI co kmin c f ->
    T + sh_rpos f <> rf_rend T co f ->
    sh_getc f = (znth txt (sh_rpos f), mkSh (sh_buf f) (sh_rpos f + 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f)).
  Proof.
    intros co kmin c f (OK & Rc & CC & KM & NS & SS) NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    unfold rf_rend in NE. unfold sh_getc. rewrite Hbuf.
    destruct (sh_stdio f) eqn:ES; cbn [negb].
    - destruct (SS eq_refl) as (N1 & N2 & N3 & N4). rewrite N1.
      destruct (Z.eqb_spec (sh_rpos f) p) as [E|NE']; [exfalso; lia|]. reflexivity.
    - reflexivity.
  Qed.

  #[using="Hp"] Lemma rf_getc_fast_lt : forall co kmin c f, RFI co kmin c f -> c <> 0 ->
    T + sh_rpos f <> rf_rend T co f -> 0 <= sh_rpos f < zlength txt.
  Proof.
    intros co kmin c f (OK & Rc & CC & KM & NS & SS) Hc NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    unfold rf_rend in NE. destruct (sh_stdio f) eqn:ES.
    - destruct (SS eq_refl) as (N1 & N2 & N3 & _). lia.
    - destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). lia.
  Qed.

  #[using="Hp"] Lemma rf_getc_fast_le : forall co kmin c f, RFI co kmin c f -> c <> 0 ->
    T + sh_rpos f <> rf_rend T co f -> 0 <= sh_rpos f <= p /\ (sh_stdio f = true -> sh_rpos f < co).
  Proof.
    intros co kmin c f (OK & Rc & CC & KM & NS & SS) Hc NE. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    unfold rf_rend in NE. destruct (sh_stdio f) eqn:ES.
    - destruct (SS eq_refl) as (N1 & N2 & N3 & _). split; [lia|]. intros _. lia.
    - destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). split; [lia|]. intros X; discriminate X.
  Qed.

  #[using="Hp T1"] Lemma rf_getc_slow : forall co kmin c f, RFI co kmin c f ->
    T + sh_rpos f = rf_rend T co f ->
    sh_stdio f = true /\ J = ssJ /\ sh_n f = p /\ sh_rpos f = co /\ 0 <= co <= p /\
    (sh_shlim_neg f = true -> co = p) /\ 0 <= sh_cnt0 f <= sh_rpos f.
  Proof.
    intros co kmin c f (OK & Rc & CC & KM & NS & SS) E. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    unfold rf_rend in E. destruct (sh_stdio f) eqn:ES.
    - destruct (SS eq_refl) as (N1 & N2 & N3 & N4). repeat split; try assumption; try lia.
    - exfalso. unfold M64 in E. lia.
  Qed.

  Ltac crush := repeat progress (repeat split; try reflexivity; try discriminate; try assumption; try lia;
                                 try lazymatch goal with |- (_ -> _) => intro end).

  #[using="p BYT Hp"] Lemma R0 : forall i, 0 <= i < Z.of_nat (length txt) -> 0 <= znth txt i < 256.
  Proof. intros i Hi. apply (proj1 (Forall_forall _ _) BYT). apply znth_In. unfold zlength. lia. Qed.

  #[using="BYT Hp Hnul"] Lemma RFI_getc : forall co kmin c f, RFI co kmin c f -> c <> 0 -> T + sh_rpos f <> rf_rend T co f ->
    RFI co (kmin + 1) (fst (sh_getc f)) (snd (sh_getc f)).
  Proof.
    intros co kmin c f RJ Hc NE. pose proof (rf_getc_fast_le co kmin c f RJ Hc NE) as [LE LT].
    destruct RJ as (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst). unfold zlength in *.
    destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
    unfold RFJ, sh_getc, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    destruct st; cbn [negb].
    - destruct (SS eq_refl) as (N1 & N2 & N3 & N4). subst n. specialize (LT eq_refl).
      destruct (Z.eqb_spec rpos p) as [E|NE']; cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]; [exfalso; lia|].
      pose proof (R0 rpos ltac:(lia)).
      assert (SN : sn = false) by (destruct sn; [specialize (N3 eq_refl); lia | reflexivity]). subst sn. specialize (KM eq_refl).
      cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. unfold zlength. crush.
    - destruct (NS eq_refl) as (N1 & N2 & N3). specialize (N3 Hc). subst sn. cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
      pose proof (R0 rpos ltac:(lia)). specialize (KM eq_refl).
      unfold zlength. crush.
      all: destruct (Z.eq_dec rpos p) as [Ep|]; [|lia]; exfalso; subst rpos; rewrite Hnul in *; lia.
  Qed.

  #[using="BYT Hp T1"] Lemma RFI_getc_slow : forall co kmin c f, RFI co kmin c f -> T + sh_rpos f = rf_rend T co f ->
    RFI (win p co) (kmin + 1) (fst (sh_getc f)) (snd (sh_getc f)).
  Proof.
    intros co kmin c f RJ E. pose proof (rf_getc_slow co kmin c f RJ E) as (ST & EJ & Hn & Hrp & Hco & Hlat & Hc0).
    pose proof (win_range p co Hco) as WR.
    destruct RJ as (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst). unfold zlength in *.
    destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf st n rpos.
    unfold RFJ, sh_getc, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg negb].
    destruct (Z.eqb_spec co p) as [E2|NE2]; cbn [fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg negb].
    - subst co. unfold zlength. crush.
    - pose proof (R0 co ltac:(lia)).
      assert (SN : sn = false) by (destruct sn; [specialize (Hlat eq_refl); lia | reflexivity]). subst sn. specialize (KM eq_refl).
      cbn [negb fst snd sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg]. unfold zlength. crush.
  Qed.

  #[using="Hp"] Lemma RFI_unget : forall co kmin c f, RFI co kmin c f -> 1 <= kmin -> RFI co (kmin - 1) c (sh_unget f).
  Proof.
    intros co kmin c f (OK & Rc & CC & KM & NS & SS) Hk. destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
    unfold RFJ, sh_unget, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    destruct sn; cbn [negb sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    - destruct st.
      + destruct (SS eq_refl) as (N1 & N2 & N3 & N4). specialize (N3 eq_refl). crush.
      + destruct (NS eq_refl) as (N1 & _). discriminate N1.
    - specialize (KM eq_refl). destruct st.
      + destruct (SS eq_refl) as (N1 & N2 & N3 & N4). crush.
      + destruct (NS eq_refl) as (N1 & N2 & N3). crush.
  Qed.

  #[using="Hp"] Lemma RFI_lim0 : forall co kmin c f, RFI co kmin c f -> RFI co 0 c (sh_lim0 f).
  Proof.
    intros co kmin c f (OK & Rc & CC & KM & NS & SS). destruct OK as (Hbuf & Rl & Rr & Rc0 & Rn & Rst).
    destruct f as [buf rpos cnt0 n st sn]. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg] in *. subst buf.
    unfold RFJ, sh_lim0, sh_ok. cbn [sh_buf sh_rpos sh_cnt0 sh_n sh_stdio sh_shlim_neg].
    destruct st.
    - destruct (SS eq_refl) as (N1 & N2 & N3 & N4). crush.
    - destruct (NS eq_refl) as (N1 & N2 & N3). crush.
  Qed.

  #[using="Type"] Lemma rf_unget_shlim : forall f, (if sh_shlim_neg f then M64 else 0) = (if sh_shlim_neg (sh_unget f) then M64 else 0).
  Proof. intros [b r c n st sn]. unfold sh_unget. cbn. destruct sn; reflexivity. Qed.
  #[using="Type"] Lemma rf_unget_eq : forall f, sh_shlim_neg f = false ->
    sh_unget f = mkSh (sh_buf f) (sh_rpos f - 1) (sh_cnt0 f) (sh_n f) (sh_stdio f) (sh_shlim_neg f).
  Proof. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
  #[using="Type"] Lemma rf_unget_nop : forall f, sh_shlim_neg f = true -> sh_unget f = f.
  Proof. intros [b r c0 n st sn] H. cbn in H. subst sn. reflexivity. Qed.
End RF.

Open Scope bv_scope.

Lemma shgetc_callJ : forall (ra : word) (q : Z) (gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (Fp T p co : Z) (J : rfj) (kmin c : Z) (f : shfile) (txt pre post : list Z) (canary : word),
  rw_cells rsegs m Fp (rf_cells T co f J) ->
  RFJ T txt p J co kmin c f ->
  (T + sh_rpos f = rf_rend T co f)%Z ->
  rtext T txt pre post -> p = zlength pre -> bytes_at rsegs m T (zbytes txt) -> ssp_cells m canary ->
  (4096 <= T)%Z -> (T + 2^41 <= 2^63)%Z -> (Fp + 232 <= T \/ T + zlength txt <= Fp)%Z ->
  stk rsegs m (q - 160) q -> (4096 <= q - 160)%Z -> (q <= Fp)%Z -> (Fp + 232 <= 2^63)%Z ->
  (T + zlength txt <= q - 160 \/ q <= T)%Z ->
  (ssp_guard + 8 <= q - 160)%Z ->
  (T + zlength txt <= got_ssp \/ got_ssp + 8 <= T)%Z -> (T + zlength txt <= ssp_guard \/ ssp_guard + 8 <= T)%Z ->
  (0 <= q)%Z -> (q < 2^63)%Z ->
  mem_inv rsegs m ->
  evt rsegs (shgetc_post ra q gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc Fp T p co f txt canary m)
    (MS (mkR ra (Z_to_bv 64 q) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SHGETC) fc None m (seg_rom rsegs)).
Proof.
  intros until canary. intros FC RJ SLOW TXT Hp BY SSP T0 T1 SEP ST SPLO SPF SPF2 SPT SG1 SG2 SG3 Q0 Q1 MI.
  pose proof RJ as RJ'. destruct RJ' as (OK & Rc & CC & KM & NS & SS).
  assert (Hp2 : (0 <= p < zlength txt)%Z).
  { destruct TXT as (Htxt & _ & _ & _). subst p txt. unfold zlength. rewrite length_app. cbn. lia. }
  destruct (rf_getc_slow T txt p J Hp2 T1 co kmin c f RJ SLOW) as (ST0 & EJ & Hn & Hrp & Hco & Hlat & Hc0).
  subst J.
  eapply shgetc_spec with (pre := pre) (post := post); try eassumption; try LiaTuning.alia.
  all: try (destruct OK as (Hbuf & _); exact Hbuf).
Qed.
