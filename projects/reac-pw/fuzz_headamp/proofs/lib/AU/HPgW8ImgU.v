(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgW8Img.v at 888d1ffb4c3; module paths fuzz_role -> fuzz_headamp, RPgBase / RPgCSpec / RPgImgA / RPgMem / RPgSeg -> HPgBase / HPgCSpec / HPgImgA / HPgMem / HPgSeg, the rl_ / rm_ / rs_ prefixes -> hd_ / hm_ / hs_. *)
(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_headamp/lib/A/HPgW8Img.v at 67d07647f9a; image B's segments (lib/AU/Img0U.v rsegs) in place of image A's, the wi_ prefix -> wiu_, and the block's old and new bytes read through two views (H2, m2) and (H3, m3), because a callee's post on image B (pod_write_ent) may end in a later world. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan): the first block's image after one pod write of the pod
   loop (pod.h:428-432): the pod's bytes at buf[len], the new len and, for the first params Struct, the record in
   ent[n_ent] and n_ent + 1; every other byte of the block as before. Proves no function (kind: segment lemma). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Import Cursor Model Layout.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgMem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgW8Model.
Import ListNotations.
Open Scope Z_scope.

Section w. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

Lemma wiu_nth_ow : forall (l x : list byte) o i d, (o + length x <= length l)%nat ->
  nth i (overwrite l o x) d = if (o <=? i)%nat && (i <? o + length x)%nat then nth (i - o) x d else nth i l d.
Proof.
  intros l x o i d Hl. unfold overwrite.
  assert (Lf : length (firstn o l) = o) by (rewrite length_firstn; lia).
  destruct (Nat.ltb_spec i o) as [Hi|Hi].
  - rewrite app_nth1 by lia. replace ((o <=? i)%nat) with false by (symmetry; apply Nat.leb_gt; lia).
    cbv beta iota. rewrite <- (firstn_skipn o l) at 2. rewrite app_nth1 by lia. reflexivity.
  - rewrite app_nth2 by lia. rewrite Lf. replace ((o <=? i)%nat) with true by (symmetry; apply Nat.leb_le; lia).
    destruct (Nat.ltb_spec i (o + length x)) as [Hj|Hj]; cbv beta iota.
    + rewrite app_nth1 by lia. reflexivity.
    + rewrite app_nth2 by lia. rewrite <- (firstn_skipn (o + length x) l) at 2.
      assert (Lg : length (firstn (o + length x) l) = (o + length x)%nat) by (rewrite length_firstn; lia).
      rewrite (app_nth2 (firstn (o + length x) l)) by lia. rewrite Lg. f_equal. lia.
Qed.

Lemma wiu_len_ow : forall (l x : list byte) o,
  length (overwrite l o x) = (Nat.min o (length l) + length x + (length l - (o + length x)))%nat.
Proof. intros l x o. unfold overwrite. rewrite !length_app, length_firstn, length_skipn. lia. Qed.

(* the bytes of l at a in (H, m), except at the addresses of S *)
Definition wiu_Q (H : word -> bool) (m : word -> option byte) (a : Z) (l : list byte) (S : Z -> Prop) : Prop :=
  forall i, (i < length l)%nat -> ~ S (a + Z.of_nat i) ->
  aview rsegs H m (a + Z.of_nat i) = Some (bv_unsigned (nth i l (Z_to_bv 8 0))).

Lemma wiu_Q_end : forall H m a l, wiu_Q H m a l (fun _ => False) -> hm_bytes rsegs H m a l.
Proof. intros H m a l Q. apply hm_bytes_aview. intros i Hi. apply Q; [exact Hi | tauto]. Qed.

Lemma wiu_Q_patch : forall H m a l o x (S : Z -> Prop),
  wiu_Q H m a l (fun y => S y \/ (a + Z.of_nat o <= y < a + Z.of_nat o + Z.of_nat (length x))) ->
  hm_bytes rsegs H m (a + Z.of_nat o) x -> (o + length x <= length l)%nat ->
  wiu_Q H m a (overwrite l o x) S.
Proof.
  intros H m a l o x S Q X Hl i Hi NS. rewrite length_overwrite in Hi by exact Hl.
  rewrite wiu_nth_ow by exact Hl.
  destruct ((o <=? i)%nat && (i <? o + length x)%nat) eqn:E.
  - apply andb_true_iff in E as [E1 E2]. apply Nat.leb_le in E1. apply Nat.ltb_lt in E2.
    pose proof (proj1 (hm_bytes_aview rsegs H m (a + Z.of_nat o) x) X (i - o)%nat ltac:(lia)) as A.
    replace (a + Z.of_nat o + Z.of_nat (i - o)) with (a + Z.of_nat i) in A by lia. exact A.
  - apply Q; [exact Hi|]. intros [HS|HW]; [exact (NS HS)|].
    apply andb_false_iff in E. destruct E as [E|E]; [apply Nat.leb_gt in E | apply Nat.ltb_ge in E]; lia.
Qed.

Lemma wiu_Q_base : forall H2 m2 H3 m3 a l (S : Z -> Prop),
  hm_bytes rsegs H2 m2 a l ->
  (forall i, (i < length l)%nat -> ~ S (a + Z.of_nat i) ->
     aview rsegs H3 m3 (a + Z.of_nat i) = aview rsegs H2 m2 (a + Z.of_nat i)) ->
  wiu_Q H3 m3 a l S.
Proof.
  intros H2 m2 H3 m3 a l S B K i Hi NS. rewrite K by assumption.
  exact (proj1 (hm_bytes_aview rsegs H2 m2 a l) B i Hi).
Qed.

Lemma wiu_ents : forall sh ps es,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es -> (length es < 32)%nat ->
  (length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\
  Forall (fun e => (length (e_body e) <= 96)%nat) (pc_ents (PbCut sh ps (Some es))).
Proof.
  intros sh ps es Hv He Hes Hq.
  assert (G : (length (pc_ents (PbCut sh ps (Some es))) <= 32)%nat /\ Forall ent_wf (pc_ents (PbCut sh ps (Some es)))).
  { unfold pc_ents, first_params. cbn [pc_props pc_open].
    destruct (find (fun kv => fst kv =? POD_PROP_PARAMS) ps) as [kv|] eqn:F; cbn [option_map].
    - apply find_some in F as [Hin _]. destruct (snd kv) as [i|l] eqn:Ek; [split; [cbn; lia | constructor] |].
      rewrite Forall_forall in Hv. pose proof (Hv kv Hin) as Hk. rewrite Ek in Hk. cbn [pval_wf] in Hk.
      split; [exact Hk|].
      apply all_ents_Forall in He. rewrite Forall_forall in He. specialize (He kv Hin). rewrite Ek in He.
      cbn [ents_of] in He. exact He.
    - split; [lia | exact Hes]. }
  destruct G as [G1 G2]. split; [exact G1|]. eapply Forall_impl; [exact wm_body_bound | exact G2].
Qed.

(* the pp block after one pod write: the pod's bytes at buf[len], the new len, and, for the first params Struct,
   the record in ent[n_ent] and n_ent + 1; every other byte of the block as before. The old image is read in
   (H2, m2), the new one in (H3, m3). *)
Lemma wiu_final : forall (H2 H3 : word -> bool) (m2 m3 : word -> option byte) (pp : Z) sh ps es ed,
  Forall (fun kv => pval_wf (snd kv)) ps -> Forall ent_wf (all_ents ps) -> Forall ent_wf es -> ent_wf ed ->
  (length ps <= 2)%nat -> (length es < 32)%nat ->
  0 <= pp -> pp + Layout.PP_SIZE <= 2 ^ 64 ->
  let L := Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) in
  let n2 := L + 8 + e_size ed + pad8 (e_size ed) in
  let first := pc_first (PbCut sh ps (Some es)) in
  let ne := Z.of_nat (length es) in
  hm_bytes rsegs H2 m2 pp (pc_image (PbCut sh ps (Some es))) ->
  hm_bytes rsegs H3 m3 (pp + L) (enc_pod ed) ->
  val_mem rsegs (mrestrict H3 m3) (pp + Layout.OFF_LEN) 8 n2 ->
  (first = true ->
     val_mem rsegs (mrestrict H3 m3) (pp + Layout.OFF_N_ENT) 4 (ne + 1) /\
     hm_bytes rsegs H3 m3 (pp + (Layout.OFF_ENT + Layout.ENT_SIZE * ne)) (ent_mem ed)) ->
  (forall a, pp <= a < pp + Layout.PP_SIZE ->
     ~ (pp + L <= a < pp + n2) ->
     ~ (pp + Layout.OFF_LEN <= a < pp + Layout.OFF_LEN + 8) ->
     (first = true ->
        ~ (pp + Layout.OFF_N_ENT <= a < pp + Layout.OFF_N_ENT + 4) /\
        ~ (pp + (Layout.OFF_ENT + Layout.ENT_SIZE * ne) <= a < pp + (Layout.OFF_ENT + Layout.ENT_SIZE * ne) + 104)) ->
     aview rsegs H3 m3 a = aview rsegs H2 m2 a) ->
  hm_bytes rsegs H3 m3 pp (pc_image (PbCut sh ps (Some (es ++ [ed])))).
Proof.
  intros H2 H3 m2 m3 pp sh ps es ed Hv He Hes Hed Hp Hq Hpp Hpp2. cbv zeta. intros B2 Bpod Vlen Hfirst K.
  destruct (wm_L0 sh ps es Hv He Hes Hp Hq) as [HL0 _].
  destruct (wm_put_bound sh ps es ed Hv He Hes Hed Hp Hq) as [Hb1 _].
  pose proof (zlen_enc_pod ed Hed) as Epod.
  pose proof (pad8_bound (e_size ed)) as Hpad.
  assert (LI : Z.of_nat (length (pc_image (PbCut sh ps (Some es)))) = PP_SIZE).
  { destruct (wiu_ents sh ps es Hv He Hes Hq) as [E1 E2].
    unfold pc_image. apply length_pp_image; [lia | exact E1 | exact E2]. }
  pose proof (hm_bytes_of_val _ _ _ _ _ _ Vlen) as Blen. fold (le64 (Z.of_nat (length (pc_buf (PbCut sh ps (Some es)))) + 8 + e_size ed + pad8 (e_size ed))) in Blen.
  rewrite <- (Z2Nat.id OFF_LEN) in Blen by (unfold OFF_LEN; lia).
  set (Ln := length (pc_buf (PbCut sh ps (Some es)))) in *.
  set (IMG := pc_image (PbCut sh ps (Some es))) in *.
  set (pod := enc_pod ed) in *.
  rewrite Nat2Z.inj_add in Hb1.
  destruct (pc_first (PbCut sh ps (Some es))) eqn:Ef.
  - destruct (Hfirst ltac:(first [exact Ef | reflexivity])) as [Vn Bent].
    pose proof (hm_bytes_of_val _ _ _ _ _ _ Vn) as Bn. fold (le32 (Z.of_nat (length es) + 1)) in Bn.
    rewrite <- (Z2Nat.id OFF_N_ENT) in Bn by (unfold OFF_N_ENT; lia).
    rewrite <- (Z2Nat.id (OFF_ENT + ENT_SIZE * Z.of_nat (length es))) in Bent by (unfold OFF_ENT, ENT_SIZE; lia).
    assert (Le : length (ent_mem ed) = 104%nat) by (apply length_ent_mem; apply wm_body_bound; exact Hed).
    rewrite (wm_img_first sh ps es ed Ef Hv He Hes Hed Hp Hq). fold Ln IMG pod.
    apply wiu_Q_end.
    apply wiu_Q_patch; [| exact Bn |].
    2:{ rewrite !wiu_len_ow, ?length_le64, ?length_le32, ?Le;
        unfold OFF_LEN, OFF_N_ENT, OFF_ENT, ENT_SIZE, PP_SIZE, POD_BUF_MAX in *; lia. }
    apply wiu_Q_patch; [| exact Bent |].
    2:{ rewrite !wiu_len_ow, ?length_le64, ?Le;
        unfold OFF_LEN, OFF_N_ENT, OFF_ENT, ENT_SIZE, PP_SIZE, POD_BUF_MAX in *; lia. }
    apply wiu_Q_patch; [| exact Blen |].
    2:{ rewrite !wiu_len_ow, ?length_le64;
        unfold OFF_LEN, PP_SIZE, POD_BUF_MAX in *; lia. }
    apply wiu_Q_patch; [| exact Bpod |].
    2:{ unfold PP_SIZE, POD_BUF_MAX in *; lia. }
    apply (wiu_Q_base H2 m2); [exact B2|]. intros i Hi NS. cbn beta in NS.
    rewrite ?length_le64, ?length_le32, ?Le in NS. rewrite !Z2Nat.id in NS by (unfold OFF_LEN, OFF_N_ENT, OFF_ENT, ENT_SIZE; lia).
    apply K.
    + unfold PP_SIZE in *; lia.
    + intro W. apply NS. right. lia.
    + intro W. apply NS. left. right. lia.
    + intros _. split.
      * intro W. apply NS. left. left. left. right. lia.
      * intro W. apply NS. left. left. right. unfold ENT_SIZE in *. lia.
  - rewrite (wm_img_other sh ps es ed Ef Hv He Hes Hed Hp Hq). fold Ln IMG pod.
    apply wiu_Q_end.
    apply wiu_Q_patch; [| exact Blen |].
    2:{ rewrite !wiu_len_ow, ?length_le64;
        unfold OFF_LEN, PP_SIZE, POD_BUF_MAX in *; lia. }
    apply wiu_Q_patch; [| exact Bpod |].
    2:{ unfold PP_SIZE, POD_BUF_MAX in *; lia. }
    apply (wiu_Q_base H2 m2); [exact B2|]. intros i Hi NS. cbn beta in NS.
    rewrite ?length_le64 in NS. rewrite !Z2Nat.id in NS by (unfold OFF_LEN; lia).
    apply K.
    + unfold PP_SIZE in *; lia.
    + intro W. apply NS. right. lia.
    + intro W. apply NS. left. right. lia.
    + intros Ht. congruence.
Qed.
End w.

Print Assumptions wiu_final.
