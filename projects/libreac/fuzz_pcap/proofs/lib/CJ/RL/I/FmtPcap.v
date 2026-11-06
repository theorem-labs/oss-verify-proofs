From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.Lib Require Exec.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.GX Require Import Printf_model Printf_text.
From OSSVerify.Proofs.libreac.fuzz_pcap.lib.CJ.RL.GX Require G_printf_core_common.
Import G_printf_core_common.G_printf_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition PRE_Z : list Z :=
  [112; 99; 97; 112; 95; 115; 111; 117; 114; 99; 101; 58; 32; 115; 107; 105; 112; 112; 105; 110; 103; 32;
   111; 118; 101; 114; 115; 105; 122; 101; 100; 32; 102; 114; 97; 109; 101; 32; 40].
Definition MID_Z : list Z := [32; 62; 32].
Definition END_Z : list Z := [32; 98; 121; 116; 101; 115; 41; 10].

Definition FMT_Z : list Z := PRE_Z ++ [37; 117] ++ MID_Z ++ [37; 122; 117] ++ END_Z ++ [0].

Definition OUT_Z (I c : Z) : list Z := PRE_Z ++ pf_udec I ++ MID_Z ++ pf_udec c ++ END_Z.

Lemma pf_digits_len : forall f x acc, (length (pf_digits f x acc) <= f + length acc)%nat.
Proof.
  induction f as [|f IH]; intros x acc; cbn [pf_digits]; [lia|].
  destruct (x <? 10); cbn [length]; [lia|]. specialize (IH (x / 10) ((48 + x mod 10) :: acc)). cbn [length] in IH. lia.
Qed.

Lemma udec_len : forall u, zlength (pf_udec u) <= 20.
Proof. intros u. unfold zlength, pf_udec. pose proof (pf_digits_len 20 u []) as H. cbn [length] in H. lia. Qed.

Lemma fmt_end : forall f cnt, 0 <= cnt -> cnt + 8 <= INT_MAX ->
  printf_pieces_loop (S (S f)) (END_Z ++ [0]) [] cnt = Some ([END_Z], cnt + zlength END_Z).
Proof.
  intros f cnt H0 H.
  apply (pt_lit_step (S f) 32 [98; 121; 116; 101; 115; 41; 10; 0] [] cnt END_Z [0] [] (cnt + zlength END_Z)).
  - lia. - reflexivity. - reflexivity. - reflexivity. - left; reflexivity.
  - change (zlength END_Z) with 8. lia.
  - reflexivity.
Qed.

Lemma fmt_zu : forall f cnt c, 0 <= c -> 0 <= cnt -> cnt + zlength (pf_udec c) + 8 <= INT_MAX ->
  exists pcs, printf_pieces_loop (S (S (S f))) (37 :: 122 :: 117 :: END_Z ++ [0]) [PA_ull c] cnt
                = Some (pcs, cnt + zlength (pf_udec c ++ END_Z)) /\ concat pcs = pf_udec c ++ END_Z.
Proof.
  intros f cnt c Hc H0 H. pose proof (pt_zlength_nonneg (pf_udec c)) as N.
  destruct (pt_conv_ull cnt T_SIZET c (or_intror eq_refl) Hc H0 ltac:(lia)) as (ps1 & C & E).
  eapply (pt_dir_glue (S (S f)) 122 (117 :: END_Z ++ [0]) _ (END_Z ++ [0]) (PA_ull c) [] cnt ps1 (pf_udec c) [END_Z] END_Z).
  - lia. - apply pt_pd_zu. - exact C. - exact E.
  - apply fmt_end; lia.
  - cbn [concat]. apply app_nil_r.
Qed.

Lemma fmt_mid : forall f cnt c, 0 <= c -> 0 <= cnt -> cnt + 3 + zlength (pf_udec c) + 8 <= INT_MAX ->
  exists pcs, printf_pieces_loop (S (S (S (S f)))) (MID_Z ++ 37 :: 122 :: 117 :: END_Z ++ [0]) [PA_ull c] cnt
                = Some (pcs, cnt + zlength (MID_Z ++ pf_udec c ++ END_Z)) /\ concat pcs = MID_Z ++ pf_udec c ++ END_Z.
Proof.
  intros f cnt c Hc H0 H. pose proof (pt_zlength_nonneg (pf_udec c)) as N.
  destruct (fmt_zu f (cnt + zlength MID_Z) c Hc ltac:(change (zlength MID_Z) with 3; lia)
              ltac:(change (zlength MID_Z) with 3; lia)) as (pcs & P & E).
  exists (MID_Z :: pcs). split.
  - apply (pt_lit_step (S (S (S f))) 32 [62; 32; 37; 122; 117; 32; 98; 121; 116; 101; 115; 41; 10; 0] [PA_ull c] cnt
             MID_Z (37 :: 122 :: 117 :: END_Z ++ [0]) pcs).
    + lia. + reflexivity. + reflexivity. + reflexivity.
    + right. split; [reflexivity|]. exists 122, (117 :: END_Z ++ [0]). split; [reflexivity | lia].
    + change (zlength MID_Z) with 3. lia.
    + rewrite P. f_equal. f_equal. rewrite !pt_zlength_app. lia.
  - cbn [concat]. rewrite E. reflexivity.
Qed.

Lemma fmt_u : forall f cnt I c, 0 <= I -> 0 <= c -> 0 <= cnt ->
  cnt + zlength (pf_udec I) + 3 + zlength (pf_udec c) + 8 <= INT_MAX ->
  exists pcs, printf_pieces_loop (S (S (S (S (S f))))) (37 :: 117 :: MID_Z ++ 37 :: 122 :: 117 :: END_Z ++ [0])
                [PA_u I; PA_ull c] cnt
                = Some (pcs, cnt + zlength (pf_udec I ++ MID_Z ++ pf_udec c ++ END_Z))
              /\ concat pcs = pf_udec I ++ MID_Z ++ pf_udec c ++ END_Z.
Proof.
  intros f cnt I c HI Hc H0 H. pose proof (pt_zlength_nonneg (pf_udec I)) as NI.
  pose proof (pt_zlength_nonneg (pf_udec c)) as Nc.
  destruct (pt_conv_u cnt I HI H0 ltac:(lia)) as (ps1 & C & E).
  destruct (fmt_mid f (cnt + zlength (pf_udec I)) c Hc ltac:(lia) ltac:(lia)) as (pcs & P & EP).
  eapply (pt_dir_glue (S (S (S (S f)))) 117 (MID_Z ++ 37 :: 122 :: 117 :: END_Z ++ [0]) _ _ (PA_u I) [PA_ull c] cnt ps1
            (pf_udec I) pcs (MID_Z ++ pf_udec c ++ END_Z)).
  - lia. - apply pt_pd_u. - exact C. - exact E.
  - exact P.
  - exact EP.
Qed.

Lemma fmt_pieces : forall I c, 0 <= I -> 0 <= c -> zlength (pf_udec I) <= 10 ->
  exists ps, printf_pieces FMT_Z [PA_u I; PA_ull c] = Some (ps, zlength (OUT_Z I c)) /\ concat ps = OUT_Z I c.
Proof.
  intros I c HI Hc HL. pose proof (udec_len c) as Lc. pose proof (pt_zlength_nonneg (pf_udec I)) as NI.
  pose proof (pt_zlength_nonneg (pf_udec c)) as Nc.
  destruct (fmt_u 50 (zlength PRE_Z) I c HI Hc ltac:(change (zlength PRE_Z) with 39; lia)
              ltac:(change (zlength PRE_Z) with 39; unfold INT_MAX; lia)) as (pcs & P & E).
  exists (PRE_Z :: pcs). split.
  - unfold printf_pieces. change (Datatypes.length FMT_Z) with (S 55).
    apply (pt_lit_step 55 112 (tl FMT_Z) [PA_u I; PA_ull c] 0 PRE_Z
             (37 :: 117 :: MID_Z ++ 37 :: 122 :: 117 :: END_Z ++ [0]) pcs).
    + lia. + reflexivity. + reflexivity. + reflexivity.
    + right. split; [reflexivity|]. exists 117, (MID_Z ++ 37 :: 122 :: 117 :: END_Z ++ [0]). split; [reflexivity | lia].
    + change (zlength PRE_Z) with 39. unfold INT_MAX. lia.
    + rewrite Z.add_0_l. rewrite P. f_equal. f_equal. unfold OUT_Z. rewrite !pt_zlength_app. lia.
  - cbn [concat]. rewrite E. reflexivity.
Qed.

Lemma fmt_model : forall I c, 0 <= I -> 0 <= c -> zlength (pf_udec I) <= 10 ->
  printf_model (St:=list Z) (OUT_snf SNF_CAP) OUTFP_snf FMT_Z [PA_u I; PA_ull c] []
    = ITree.Ret (Ok (zlength (OUT_Z I c), OUT_Z I c)).
Proof.
  intros I c HI Hc HL. destruct (fmt_pieces I c HI Hc HL) as (ps & P & E).
  rewrite <- E at 2. apply printf_model_snf_pieces; [exact P|].
  rewrite E. pose proof (udec_len c) as Lc. unfold OUT_Z. rewrite !pt_zlength_app.
  change (zlength PRE_Z) with 39. change (zlength MID_Z) with 3. change (zlength END_Z) with 8.
  unfold SNF_CAP. lia.
Qed.

Lemma fmt_pass1 : pass1_ok FMT_Z = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fmt_bytes : Forall (fun c => 0 <= c < 256) FMT_Z.
Proof. unfold FMT_Z, PRE_Z, MID_Z, END_Z. cbn [app]. repeat (apply Forall_cons; [cbv beta; lia|]). apply Forall_nil. Qed.

Lemma fmt_len : zlength FMT_Z = 56.
Proof. reflexivity. Qed.

Lemma fmt_fp : forall I c, fp_calls (Datatypes.length FMT_Z) FMT_Z [PA_u I; PA_ull c] = [].
Proof. intros I c. apply pt_fp_nog. repeat constructor. Qed.

Lemma out_len : forall I c, zlength (pf_udec I) <= 10 -> zlength (OUT_Z I c) <= 80.
Proof.
  intros I c HL. pose proof (udec_len c). unfold OUT_Z. rewrite !pt_zlength_app.
  change (zlength PRE_Z) with 39. change (zlength MID_Z) with 3. change (zlength END_Z) with 8. lia.
Qed.

Lemma implM_ret_evt : forall segs {S A : Type} (cm : M S A) s a s' Q ms,
  cm s = ITree.Ret (Ok (a, s')) -> implM segs cm s Q ms -> Exec.evt segs (Q a s') ms.
Proof. intros segs S A cm s a s' Q ms E H. unfold implM in H. rewrite E in H. exact H. Qed.

Lemma model_evt : forall segs I c Q ms, 0 <= I -> 0 <= c -> zlength (pf_udec I) <= 10 ->
  implM segs (printf_model (St:=list Z) (OUT_snf SNF_CAP) OUTFP_snf FMT_Z [PA_u I; PA_ull c]) [] Q ms ->
  Exec.evt segs (Q (zlength (OUT_Z I c)) (OUT_Z I c)) ms.
Proof. intros segs I c Q ms HI Hc HL H. exact (implM_ret_evt segs _ _ _ _ _ _ (fmt_model I c HI Hc HL) H). Qed.
