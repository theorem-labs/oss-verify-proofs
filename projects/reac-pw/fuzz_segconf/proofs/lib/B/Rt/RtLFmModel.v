(* Modified by Theorem Labs, 2026-10: the image-B copy (fuzz_segconf.asan-ubsan, pin c3796c0b38f3, twin 80e82127e8ca) of lib/A/Rt/RtLFmModel.v, derived mechanically (derive_y.py b7b132fb12a7; every changed numeral checked against alreloc.py a5c53bb2bed4 and against image B), with its module paths changed (lib/A to lib/B) and its addresses moved to reac-pw/fuzz_segconf's ASan+UBSan build. The comments are the A file's. *)
(* Rows 6-9 of the interceptor interface (provenance/evidence/interceptors/INTERFACE-A-interceptors.md), their
   answers in the spine's terms (lib/Spec/SegModel.v): the bridges from RtSeg.v's posts of strchr, strncasecmp,
   strstr and isalnum (RtLStrchr.v, RtLStrncasecmp.v, RtLStrstr.v, RtLIsalnum.v) to SegModel.strchr, strncasecmp,
   strstr_found and isalnum. Proves no function (Gallina only, no machine walk); lib/Spec/SegBridge.v states the same
   bridges for the plain build's leaf contracts.

   RtSeg states a string's bytes as their values (RtSeg.ZS s, a list with no 0), SegModel as a list Z standing for the
   bytes before the NUL (SegModel.v:13-14): the same list.
   1. seg_isalnum_model: RtSeg.alnum_b is SegModel.isalnum on a byte.
   2. seg_strchr_model: strchr's answer register (RtSeg.astrchr_realizes' post, 0 < c) is x + SegModel.strchr's index,
      else 0.
   3. seg_strncasecmp_model: RtSeg.strncase_eq <-> SegModel.strncasecmp = 0 (bytes 1..255).
   4. seg_strstr_found / seg_strstr_model / seg_strstr_index: strstr's answer register (RtSeg.astrstr_realizes' post,
      0 < x) is nonzero exactly when SegModel.strstr_found, and is then x + the first index where the needle
      starts. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require YG0d.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Rt Require RtSeg.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
Import ListNotations.
Local Unset Lia Cache. Local Unset Nia Cache.
Open Scope Z_scope.

Module SM := OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec.SegModel.

(* the values of a string's bytes: 1..255 *)
Definition byte_vals (l : list Z) : Prop := forall v, In v l -> 0 < v < 256.

Lemma byte_vals_nulfree : forall l, byte_vals l -> SM.nulfree l.
Proof. intros l H Hin. specialize (H 0 Hin). lia. Qed.

Lemma byte_vals_tl : forall a l, byte_vals (a :: l) -> byte_vals l.
Proof. intros a l H v Hv. apply H. right. exact Hv. Qed.

Lemma byte_vals_hd : forall a l, byte_vals (a :: l) -> 0 < a < 256.
Proof. intros a l H. apply H. left. reflexivity. Qed.

(* two answers that differ as numbers below 2^64 differ as words *)
Lemma w64_inj : forall a b, 0 <= a < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> YG0d.w64 a = YG0d.w64 b -> a = b.
Proof.
  intros a b Ha Hb E. apply (f_equal (@bv_unsigned 64)) in E. unfold YG0d.w64 in E.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 64) with (2 ^ 64) in E.
  rewrite !Z.mod_small in E by lia. exact E.
Qed.

(* ---- 1. isalnum ---- *)

Lemma seg_isalnum_model : forall c, 0 <= c < 256 -> RtSeg.alnum_b c = SM.isalnum c.
Proof.
  intros c Hc.
  assert (H : forallb (fun z => Bool.eqb (RtSeg.alnum_b z) (SM.isalnum z)) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Bool.eqb_prop. apply H. apply in_map_iff. exists (Z.to_nat c).
  split; [lia|]. apply in_seq. lia.
Qed.

(* ---- 2. strchr ---- *)

Lemma strchr_none : forall l c, ~ In c l -> SM.strchr l c = None.
Proof.
  induction l as [|b l IH]; intros c H; [reflexivity|]. cbn [SM.strchr].
  destruct (Z.eqb_spec b c) as [->|_]; [exfalso; apply H; left; reflexivity|].
  destruct (b =? 0); [reflexivity|].
  rewrite IH; [reflexivity | intros Hin; apply H; right; exact Hin].
Qed.

Lemma strchr_first : forall l c j, SM.nulfree l -> RtSeg.first_at l c j -> SM.strchr l c = Some j.
Proof.
  induction l as [|b l IH]; intros c j Hn (Hj & Hc & Hm); [cbn in Hj; lia|].
  apply SM.nulfree_cons in Hn as [Hb Hl]. cbn [SM.strchr].
  destruct j as [|j].
  - cbn [nth] in Hc. subst c. rewrite Z.eqb_refl. reflexivity.
  - cbn [nth] in Hc. cbn [firstn In] in Hm.
    destruct (Z.eqb_spec b c) as [->|_]; [exfalso; apply Hm; left; reflexivity|].
    destruct (Z.eqb_spec b 0) as [->|_]; [exfalso; apply Hb; reflexivity|].
    rewrite (IH c j Hl); [reflexivity|].
    split; [cbn [length] in Hj; lia|]. split; [exact Hc|]. intros Hin. apply Hm. right. exact Hin.
Qed.

(* strchr's answer register (RtSeg.astrchr_realizes, its post on a byte value 0 < c) is SegModel's answer *)
Lemma seg_strchr_model : forall (x c : Z) (l : list Z) (w : bv 64), 0 < c -> SM.nulfree l ->
  ((w = YG0d.w64 0 /\ ~ In c l) \/ (exists j, RtSeg.first_at l c j /\ w = YG0d.w64 (x + Z.of_nat j))) ->
  w = YG0d.w64 (match SM.strchr l c with Some i => x + Z.of_nat i | None => 0 end).
Proof.
  intros x c l w Hc Hn [(-> & Hni) | (j & Hf & ->)].
  - rewrite (strchr_none l c Hni). reflexivity.
  - rewrite (strchr_first l c j Hn Hf). reflexivity.
Qed.

(* ---- 3. strncasecmp ---- *)

Lemma seg_lc_tolower : forall c, 0 <= c < 256 -> RtSeg.lc c = SM.tolower c.
Proof.
  intros c Hc.
  assert (H : forallb (fun z => Z.eqb (RtSeg.lc z) (SM.tolower z)) (map Z.of_nat (seq 0 256)) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in H. apply Z.eqb_eq. apply H. apply in_map_iff. exists (Z.to_nat c).
  split; [lia|]. apply in_seq. lia.
Qed.

Lemma lc_pos : forall x, 0 < x -> 0 < RtSeg.lc x.
Proof. intros x H. unfold RtSeg.lc. destruct ((65 <=? x) && (x <=? 90)); lia. Qed.

Lemma lc_0 : RtSeg.lc 0 = 0.
Proof. reflexivity. Qed.

Lemma tolower_0 : SM.tolower 0 = 0.
Proof. reflexivity. Qed.

(* lib/Spec/SegBridge.v:344 ncase_go, with RtSeg.lc for the plain build's zlower *)
Lemma ncase_go : forall n L R, byte_vals L -> byte_vals R ->
  (SM.strncasecmp_go L R n = 0 <->
   map RtSeg.lc (firstn (S n) (L ++ [0])) = map RtSeg.lc (firstn (S n) (R ++ [0]))).
Proof.
  induction n as [|n IH]; intros L R HL HR;
    destruct L as [|a L], R as [|b R]; cbn [SM.strncasecmp_go SM.hd0 app firstn map].
  - rewrite tolower_0. split; intros _; reflexivity.
  - pose proof (byte_vals_hd b R HR) as Hb.
    rewrite tolower_0, lc_0, <- (seg_lc_tolower b) by lia. pose proof (lc_pos b ltac:(lia)) as Pb.
    split; intros H; [exfalso; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; lia].
  - pose proof (byte_vals_hd a L HL) as Ha.
    rewrite tolower_0, lc_0, <- (seg_lc_tolower a) by lia. pose proof (lc_pos a ltac:(lia)) as Pa.
    split; intros H; [exfalso; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; lia].
  - pose proof (byte_vals_hd a L HL) as Ha. pose proof (byte_vals_hd b R HR) as Hb.
    rewrite <- (seg_lc_tolower a), <- (seg_lc_tolower b) by lia.
    split; intros H; [f_equal; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; lia].
  - rewrite tolower_0. split; intros _; reflexivity.
  - pose proof (byte_vals_hd b R HR) as Hb.
    rewrite tolower_0, lc_0, <- (seg_lc_tolower b) by lia. pose proof (lc_pos b ltac:(lia)) as Pb.
    split; intros H; [exfalso; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; lia].
  - pose proof (byte_vals_hd a L HL) as Ha.
    rewrite tolower_0, lc_0, <- (seg_lc_tolower a) by lia. pose proof (lc_pos a ltac:(lia)) as Pa.
    split; intros H; [exfalso; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; lia].
  - pose proof (byte_vals_hd a L HL) as Ha. pose proof (byte_vals_hd b R HR) as Hb.
    pose proof (byte_vals_tl a L HL) as HL'. pose proof (byte_vals_tl b R HR) as HR'.
    destruct (Z.eqb_spec a 0) as [E0|_]; [lia|]. destruct (Z.eqb_spec b 0) as [E0|_]; [lia|].
    rewrite <- (seg_lc_tolower a), <- (seg_lc_tolower b) by lia. cbn [negb andb].
    destruct (Z.eqb_spec (RtSeg.lc a) (RtSeg.lc b)) as [E|E].
    + destruct (a =? b); cbn [orb];
        (rewrite (IH L R HL' HR'), E;
         split; [intros H; rewrite H; reflexivity | intros H; apply (f_equal (@tl Z)) in H; exact H]).
    + assert (Eab : (a =? b) = false) by (apply Z.eqb_neq; intros ->; apply E; reflexivity).
      rewrite Eab. cbn [orb].
      split; intros H; [exfalso; lia | apply (f_equal (hd 0)) in H; cbn [hd] in H; exfalso; exact (E H)].
Qed.

(* strncasecmp's answer (RtSeg.astrncasecmp_realizes' post) in SegModel's terms *)
Lemma seg_strncasecmp_model : forall n l1 l2, byte_vals l1 -> byte_vals l2 ->
  (RtSeg.strncase_eq n l1 l2 <-> SM.strncasecmp l1 l2 n = 0).
Proof.
  intros n l1 l2 H1 H2. unfold RtSeg.strncase_eq. destruct n as [|k].
  - cbn [firstn map SM.strncasecmp]. split; intros _; reflexivity.
  - change (SM.strncasecmp l1 l2 (S k)) with (SM.strncasecmp_go l1 l2 k).
    rewrite (ncase_go k l1 l2 H1 H2). reflexivity.
Qed.

(* ---- 4. strstr ---- *)

Lemma prefixb_spec : forall p l, SM.prefixb p l = true <-> (length p <= length l)%nat /\ firstn (length p) l = p.
Proof.
  induction p as [|a p IH]; intros l; cbn [SM.prefixb length firstn].
  - split; intros _; [split; [lia | reflexivity] | reflexivity].
  - destruct l as [|b l]; cbn [length firstn].
    + split; [discriminate | intros (H & _); lia].
    + rewrite andb_true_iff, Z.eqb_eq, (IH l). split.
      * intros (-> & Hl & Hf). split; [lia|]. rewrite Hf. reflexivity.
      * intros (Hl & He). injection He as -> Hf. split; [reflexivity | split; [lia | exact Hf]].
Qed.

Lemma occ_at_prefixb : forall t w j,
  RtSeg.occ_at t w j <-> (j <= length t)%nat /\ SM.prefixb w (skipn j t) = true.
Proof.
  intros t w j. unfold RtSeg.occ_at. rewrite prefixb_spec, length_skipn. split.
  - intros (H1 & H2). split; [lia|]. split; [lia | exact H2].
  - intros (H1 & H2 & H3). split; [lia | exact H3].
Qed.

Lemma infixb_occ : forall t w, SM.infixb w t = true <-> exists j, RtSeg.occ_at t w j.
Proof.
  induction t as [|b t IH]; intros w; cbn [SM.infixb]; rewrite orb_true_iff.
  - split.
    + intros [H|H]; [exists 0%nat; apply occ_at_prefixb; split; [cbn; lia | exact H] | discriminate].
    + intros (j & Hj). apply occ_at_prefixb in Hj as (Hj & Hp). left. cbn [length] in Hj.
      replace j with 0%nat in Hp by lia. exact Hp.
  - rewrite IH. split.
    + intros [H|(j & Hj)].
      * exists 0%nat. apply occ_at_prefixb. split; [lia | exact H].
      * exists (S j). apply occ_at_prefixb in Hj as (Hj & Hp). apply occ_at_prefixb.
        cbn [length skipn]. split; [lia | exact Hp].
    + intros (j & Hj). apply occ_at_prefixb in Hj as (Hj & Hp). destruct j as [|j].
      * left. exact Hp.
      * right. exists j. apply occ_at_prefixb. cbn [length skipn] in Hj, Hp. split; [lia | exact Hp].
Qed.

(* SegModel.strstr_found on a NUL-free haystack: the needle occurs *)
Lemma seg_strstr_found : forall t w, SM.nulfree t ->
  (SM.strstr_found t w = true <-> exists j, RtSeg.occ_at t w j).
Proof. intros t w Hn. unfold SM.strstr_found. rewrite (SM.cut_nul_id t Hn). apply infixb_occ. Qed.

(* strstr's answer register (RtSeg.astrstr_realizes' post, 0 < x) is nonzero exactly when SegModel.strstr_found *)
Lemma seg_strstr_model : forall x t w (r : bv 64), 0 < x -> x + Z.of_nat (length t) < 2 ^ 64 -> SM.nulfree t ->
  ((r = YG0d.w64 0 /\ RtSeg.no_occ t w) \/ (exists j, RtSeg.first_occ t w j /\ r = YG0d.w64 (x + Z.of_nat j))) ->
  (r <> YG0d.w64 0 <-> SM.strstr_found t w = true).
Proof.
  intros x t w r Hx Hxt Hn [(-> & Hno) | (j & (Ho & _) & ->)]; rewrite (seg_strstr_found t w Hn).
  - split; [intros H; exfalso; exact (H eq_refl) | intros (j & Hj); exfalso; exact (Hno j Hj)].
  - split; [intros _; exists j; exact Ho|]. intros _ E.
    pose proof (proj1 Ho) as Hj.
    apply w64_inj in E; lia.
Qed.

(* and its value: x + the first index where the needle starts, in SegModel.prefixb's words (lib/Spec/SegBridge.v
   bridge_strstr_val's form) *)
Lemma seg_strstr_index : forall t w j, RtSeg.first_occ t w j ->
  SM.prefixb w (skipn j t) = true /\ (forall j', (j' < j)%nat -> SM.prefixb w (skipn j' t) = false).
Proof.
  intros t w j (Ho & Hm). apply occ_at_prefixb in Ho as (Hj & Hp). split; [exact Hp|].
  intros j' Hj'. destruct (SM.prefixb w (skipn j' t)) eqn:E; [|reflexivity].
  exfalso. apply (Hm j' Hj'). apply occ_at_prefixb. split; [lia | exact E].
Qed.
