(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Lib Require Import ITree.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.Spec Require Import Prelim Monad PrintfModel PrintfFormats.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.PG Require Import Printf_lib F_printf_iface Printf_pieces Printf_sn.
From OSSVerify.Proofs.leptonica.graymorph_fuzzer.lib.K5.G3 Require Import LeptFormats Printf_sn2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
Lemma digits_aux_dec_range : forall f x acc,
  Forall (fun c => 48 <= c <= 57) acc -> Forall (fun c => 48 <= c <= 57) (digits_aux f 10 (fun v => 48 + v) x acc).
Proof.
  induction f as [|f IH]; intros x acc H; [exact H|]. rewrite digits_aux_S.
  destruct (x =? 0); [exact H|]. apply IH. constructor; [|exact H].
  pose proof (Z.mod_pos_bound x 10 ltac:(lia)). lia.
Qed.
Lemma dec_digits_range : forall x, Forall (fun c => 48 <= c <= 57) (dec_digits x).
Proof. intros x. unfold dec_digits. apply digits_aux_dec_range. constructor. Qed.

(* [comment removed for export] *)
Definition DIR_s  : dir := {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 115; d_ty := T_PTR |}.
Definition DIR_d  : dir := {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 100; d_ty := T_INT |}.
Definition DIR_zu : dir := {| d_fl := 0; d_w := 0; d_p := -1; d_xp := false; d_t := 117; d_ty := T_SIZET |}.

(* [comment removed for export] *)
Lemma tail_pieces_neg : forall cnt p body, 0 <= cnt -> 1 <= zlength body -> p <= zlength body -> cnt + 1 + zlength body <= INT_MAX ->
  tail_pieces cnt 0 0 p [45] body = Some ([[45]; body], cnt + (1 + zlength body)).
Proof.
  intros cnt p body Hc Hb Hp HI. unfold tail_pieces. cbv zeta. change (zlength [45]) with 1.
  replace (Z.max p (zlength body)) with (zlength body) by lia.
  replace (INT_MAX - 1 <? zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
  replace (Z.max 0 (1 + zlength body)) with (1 + zlength body) by lia.
  replace (INT_MAX - cnt <? 1 + zlength body) with false by (symmetry; apply Z.ltb_ge; lia).
  unfold pad_pieces.
  rewrite !Z.leb_refl. cbn [orb negb Z.land Z.lxor Z.lor Z.eqb Z.lnot ZERO_PAD LEFT_ADJ]. reflexivity.
Qed.

Definition d_pieces (i : Z) : list (list Z) :=
  if i =? 0 then [[]; [48]; []] else if i <? 0 then [[45]; dec_digits (- i)] else [[]; dec_digits i].
Definition d_len (i : Z) : Z :=
  if i =? 0 then 1 else if i <? 0 then 1 + zlength (dec_digits (- i)) else zlength (dec_digits i).

(* [comment removed for export] *)
Lemma conv_pieces_d : forall cnt i, 0 <= cnt -> -2^31 <= i < 2^31 -> cnt + 21 <= INT_MAX ->
  conv_pieces cnt DIR_d (PA_i i) = Some (d_pieces i, cnt + d_len i).
Proof.
  intros cnt i Hc Hi HI. unfold d_pieces, d_len, DIR_d.
  unfold conv_pieces. cbn [d_fl d_w d_p d_xp d_t d_ty].
  change (Z.land 0 LEFT_ADJ =? 0) with true. cbv iota.
  change (negb (T_INT =? T_INT)) with false. cbv iota.
  change (negb (Z.land 0 MARK_POS =? 0)) with false. change (negb (Z.land 0 PAD_POS =? 0)) with false. cbv iota.
  destruct (Z.eqb_spec i 0) as [->|NZ].
  - change (0 mod 2 ^ 64) with 0. change (INTMAX_MAX <? 0) with false. cbv iota. cbv beta iota.
    unfold int_pieces. cbn [andb Z.eqb]. rewrite dec_digits_0. change (zlength (@nil Z)) with 0.
    change (Z.max (-1) (0 + 1)) with 1. apply tail_pieces_zero1; lia.
  - destruct (Z.ltb_spec i 0) as [NEG|POS].
    + assert (E1 : i mod 2 ^ 64 = i + 2 ^ 64).
      { rewrite <- (Z.mod_small (i + 2^64) (2^64)) by lia. rewrite <- Z.add_mod_idemp_r by lia. rewrite Z.mod_same by lia. rewrite Z.add_0_r. reflexivity. }
      rewrite E1. replace (INTMAX_MAX <? i + 2 ^ 64) with true by (symmetry; apply Z.ltb_lt; unfold INTMAX_MAX; lia). cbv iota. cbv beta iota.
      assert (E2 : (- (i + 2 ^ 64)) mod 2 ^ 64 = - i).
      { replace (- (i + 2^64)) with (- i + (-1) * 2^64) by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
      rewrite E2. unfold int_pieces. cbn [andb].
      replace (- i =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. cbv iota.
      pose proof (dec_digits_nz (- i) ltac:(lia)) as NE. pose proof (dec_digits_zlength (- i)) as DL.
      assert (L1 : 1 <= zlength (dec_digits (- i))) by (destruct (dec_digits (- i)); [contradiction | unfold zlength; cbn; lia]).
      rewrite Z.add_0_r. rewrite tail_pieces_neg by lia. reflexivity.
    + rewrite Z.mod_small by lia. replace (INTMAX_MAX <? i) with false by (symmetry; apply Z.ltb_ge; unfold INTMAX_MAX; lia). cbv iota. cbv beta iota.
      unfold int_pieces. cbn [andb].
      replace (i =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [andb]. cbv iota.
      pose proof (dec_digits_nz i ltac:(lia)) as NE. pose proof (dec_digits_zlength i) as DL.
      assert (L1 : 1 <= zlength (dec_digits i)) by (destruct (dec_digits i); [contradiction | unfold zlength; cbn; lia]).
      rewrite Z.add_0_r. rewrite tail_pieces_plain by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition lept_arg_ok (k : lkind) (a : parg) : Prop :=
  match k, a with
  | LK_s, PA_s s => Forall (fun c => 0 < c < 256) s /\ zlength s < 96
  | LK_d, PA_i i => -2^31 <= i < 2^31
  | LK_zu, PA_z u => 0 <= u < 2^64
  | _, _ => False
  end.

Definition kind_dir (k : lkind) : dir := match k with LK_s => DIR_s | LK_d => DIR_d | LK_zu => DIR_zu end.
Definition kind_max (k : lkind) : Z := match k with LK_s => 95 | LK_d => 21 | LK_zu => 20 end.

Definition byte_ok (c : Z) : Prop := 0 <= c < 256.

Lemma Forall_digit_byte : forall l, Forall (fun c => 48 <= c <= 57) l -> Forall byte_ok l.
Proof. intros l H. eapply Forall_impl; [|exact H]. intros c Hc. cbv beta in Hc. unfold byte_ok. lia. Qed.

Lemma conv_kind : forall k a cnt, lept_arg_ok k a -> 0 <= cnt -> cnt + 96 <= INT_MAX ->
  exists ps1 n, conv_pieces cnt (kind_dir k) a = Some (ps1, cnt + n) /\ n = zlength (concat ps1)
                /\ 0 <= n <= kind_max k /\ Forall byte_ok (concat ps1).
Proof.
  intros k a cnt Hok Hc HI. destruct k, a; cbn [lept_arg_ok] in Hok; try contradiction.
  - (* [comment removed for export] *) destruct Hok as [Hs Hl]. pose proof (zlength_nonneg' s) as H0.
    exists [[]; s], (zlength s). cbn [kind_dir kind_max]. unfold DIR_s. rewrite conv_pieces_s by lia.
    cbn [concat]. rewrite app_nil_l, app_nil_r. repeat split; try lia.
    eapply Forall_impl; [|exact Hs]. intros c Hcc. cbv beta in Hcc. unfold byte_ok. lia.
  - (* [comment removed for export] *) exists (d_pieces i), (d_len i). cbn [kind_dir kind_max]. rewrite conv_pieces_d by lia.
    unfold d_pieces, d_len.
    destruct (i =? 0).
    { cbn [concat]. repeat split; try (cbn; lia). repeat constructor; unfold byte_ok; lia. }
    destruct (i <? 0).
    + pose proof (dec_digits_zlength (- i)). cbn [concat]. rewrite app_nil_r. change ([45] ++ dec_digits (- i)) with (45 :: dec_digits (- i)).
      repeat split; try lia.
      * unfold zlength in *. cbn [length]. lia.
      * constructor; [unfold byte_ok; lia|]. apply Forall_digit_byte, dec_digits_range.
    + pose proof (dec_digits_zlength i). cbn [concat]. rewrite app_nil_l, app_nil_r. repeat split; try lia.
      apply Forall_digit_byte, dec_digits_range.
  - (* [comment removed for export] *) exists (if u =? 0 then [[]; [48]; []] else [[]; dec_digits u]), (if u =? 0 then 1 else zlength (dec_digits u)).
    cbn [kind_dir kind_max]. unfold DIR_zu. rewrite conv_pieces_zu by lia.
    destruct (u =? 0).
    { cbn [concat]. repeat split; try (cbn; lia). repeat constructor; unfold byte_ok; lia. }
    pose proof (dec_digits_zlength u). cbn [concat]. rewrite app_nil_l, app_nil_r. repeat split; try lia.
    apply Forall_digit_byte, dec_digits_range.
Qed.

(* [comment removed for export] *)
Definition dir_eqb (d e : dir) : bool :=
  (d_fl d =? d_fl e) && (d_w d =? d_w e) && (d_p d =? d_p e) && Bool.eqb (d_xp d) (d_xp e) && (d_t d =? d_t e) && (d_ty d =? d_ty e).
Lemma dir_eqb_eq : forall d e, dir_eqb d e = true -> d = e.
Proof.
  intros [a1 a2 a3 a4 a5 a6] [b1 b2 b3 b4 b5 b6] H. unfold dir_eqb in H. cbn [d_fl d_w d_p d_xp d_t d_ty] in H.
  rewrite !andb_true_iff in H. destruct H as (((((H1 & H2) & H3) & H4) & H5) & H6).
  apply Z.eqb_eq in H1, H2, H3, H5, H6. apply eqb_prop in H4. subst. reflexivity.
Qed.

Definition byte_okb (c : Z) : bool := (0 <=? c) && (c <? 256).
Lemma byte_okb_ok : forall l, forallb byte_okb l = true -> Forall byte_ok l.
Proof.
  intros l H. apply Forall_forall. intros c Hc. rewrite forallb_forall in H. specialize (H c Hc).
  unfold byte_okb in H. apply andb_prop in H. destruct H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. unfold byte_ok. lia.
Qed.

Fixpoint shape_bound (fuel : nat) (s : list Z) (kinds : list lkind) {struct fuel} : option Z :=
  match fuel with
  | O => None
  | S fuel' =>
    match s with
    | [] => None
    | c :: _ =>
      if c =? 0 then (match kinds with [] => Some 0 | _ :: _ => None end) else
      let lit := lit_run s in
      let l := zlength lit in
      let s1 := skipn (Datatypes.length lit) s in
      match s1 with
      | [] => None
      | c1 :: s2 =>
        if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
        else if 0 <? l then
          (if forallb byte_okb lit
           then match shape_bound fuel' s1 kinds with Some B => Some (l + B) | None => None end
           else None)
        else
          match parse_dir s2, kinds with
          | Some (d, s3), k :: kinds' =>
              if dir_eqb d (kind_dir k)
              then match shape_bound fuel' s3 kinds' with Some B => Some (kind_max k + B) | None => None end
              else None
          | _, _ => None
          end
      end
    end
  end.

Lemma shape_bound_unfold : forall fuel s kinds,
  shape_bound (S fuel) s kinds =
    match s with
    | [] => None
    | c :: _ =>
      if c =? 0 then (match kinds with [] => Some 0 | _ :: _ => None end) else
      let lit := lit_run s in
      let l := zlength lit in
      let s1 := skipn (Datatypes.length lit) s in
      match s1 with
      | [] => None
      | c1 :: s2 =>
        if (c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end then None
        else if 0 <? l then
          (if forallb byte_okb lit
           then match shape_bound fuel s1 kinds with Some B => Some (l + B) | None => None end
           else None)
        else
          match parse_dir s2, kinds with
          | Some (d, s3), k :: kinds' =>
              if dir_eqb d (kind_dir k)
              then match shape_bound fuel s3 kinds' with Some B => Some (kind_max k + B) | None => None end
              else None
          | _, _ => None
          end
      end
    end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ppl_shape : forall fuel s kinds args cnt B,
  shape_bound fuel s kinds = Some B -> Forall2 lept_arg_ok kinds args -> 0 <= cnt -> cnt + B <= 2^30 ->
  exists ps r, printf_pieces_loop fuel s args cnt = Some (ps, r) /\ r = cnt + zlength (concat ps)
               /\ 0 <= zlength (concat ps) <= B /\ Forall byte_ok (concat ps).
Proof.
  induction fuel as [|fuel IH]; intros s kinds args cnt B SB FA Hc HB; [discriminate|].
  rewrite shape_bound_unfold in SB. rewrite ppl_unfold.
  destruct s as [|c s1]; [discriminate|].
  destruct (c =? 0).
  { destruct kinds; [|discriminate]. inversion SB; subst. exists [], cnt. cbn [concat]. rewrite zlength_nil.
    repeat split; try lia. constructor. }
  cbv zeta in SB. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  pose proof (zlength_nonneg' lit) as Hl0.
  destruct (0 <? zlength lit).
  - destruct (forallb byte_okb lit) eqn:FB; [|discriminate].
    destruct (shape_bound fuel (c1 :: s2) kinds) as [B'|] eqn:SB'; [|discriminate]. inversion SB; subst B. clear SB.
    destruct (IH _ _ _ (cnt + zlength lit) _ SB' FA ltac:(lia) ltac:(lia)) as (ps & r & P & Hr & Hz & Hby).
    replace (INT_MAX - cnt <? zlength lit) with false by (symmetry; apply Z.ltb_ge; unfold INT_MAX; lia).
    rewrite P. exists (lit :: ps), r. cbn [concat]. rewrite zlength_app.
    repeat split; try lia. apply Forall_app. split; [apply byte_okb_ok; exact FB | exact Hby].
  - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct kinds as [|k kinds']; [discriminate|].
    destruct (dir_eqb d (kind_dir k)) eqn:DE; [|discriminate]. apply dir_eqb_eq in DE. subst d.
    destruct (shape_bound fuel s3 kinds') as [B'|] eqn:SB'; [|discriminate]. inversion SB; subst B. clear SB.
    inversion FA as [|k0 a kk args' Hka FA' E1 E2]; subst.
    assert (HB0 : 0 <= B').
    { destruct (IH _ _ _ 0 _ SB' FA' ltac:(lia) ltac:(destruct k; cbn [kind_max] in HB; lia)) as (ps0 & r0 & _ & _ & Hz & _). lia. }
    destruct (conv_kind k a cnt Hka Hc ltac:(unfold INT_MAX; destruct k; cbn [kind_max] in HB; lia)) as (ps1 & n & C & Hn & Hnr & Hby1).
    rewrite C.
    destruct (IH _ _ _ (cnt + n) _ SB' FA' ltac:(lia) ltac:(lia)) as (ps & r & P & Hr & Hz & Hby).
    rewrite P. exists ([] :: ps1 ++ ps), r. cbn [concat]. rewrite app_nil_l, concat_app, zlength_app.
    repeat split; try lia. apply Forall_app. split; assumption.
Qed.

(* [comment removed for export] *)
Lemma fp_shape : forall fuel s kinds args B,
  shape_bound fuel s kinds = Some B -> Forall2 lept_arg_ok kinds args -> fp_calls fuel s args = [].
Proof.
  induction fuel as [|fuel IH]; intros s kinds args B SB FA; [reflexivity|].
  rewrite shape_bound_unfold in SB. cbn [fp_calls].
  destruct s as [|c s1]; [reflexivity|].
  destruct (c =? 0); [reflexivity|].
  cbv zeta in SB. cbv zeta. remember (lit_run (c :: s1)) as lit eqn:Hlit. clear Hlit.
  destruct (skipn (Datatypes.length lit) (c :: s1)) as [|c1 s2]; [discriminate|].
  destruct ((c1 =? 37) && match s2 with [] => true | c2 :: _ => c2 =? 37 end)%bool; [discriminate|].
  destruct (0 <? zlength lit).
  - destruct (forallb byte_okb lit); [|discriminate].
    destruct (shape_bound fuel (c1 :: s2) kinds) as [B'|] eqn:SB'; [|discriminate]. exact (IH _ _ _ _ SB' FA).
  - destruct (parse_dir s2) as [[d s3]|]; [|discriminate]. destruct kinds as [|k kinds']; [discriminate|].
    destruct (dir_eqb d (kind_dir k)); [|discriminate].
    destruct (shape_bound fuel s3 kinds') as [B'|] eqn:SB'; [|discriminate].
    inversion FA as [|k0 a kk args' Hka FA' E1 E2]; subst.
    destruct k, a; cbn [lept_arg_ok] in Hka; try contradiction; exact (IH _ _ _ _ SB' FA').
Qed.

(* [comment removed for export] *)
Definition fmt_check (fk : list Z * list lkind) : bool :=
  pass1_ok (fst fk) &&
  match shape_bound (Datatypes.length (fst fk)) (fst fk) (snd fk) with Some B => B <=? 512 | None => false end.

Lemma lept_fmts_checked : forallb fmt_check LEPT_FMT_LIST = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Theorem lept_model_run : forall fmt kinds args,
  In (fmt, kinds) LEPT_FMT_LIST -> Forall2 lept_arg_ok kinds args ->
  pass1_ok fmt = true /\ fp_calls (Datatypes.length fmt) fmt args = [] /\
  exists r d o, printf_model OUT_sn2 OUTFP_sn2 fmt args ([], []) = ITree.Ret (Ok (r, (d, o)))
                /\ r = zlength (d ++ o) /\ zlength (d ++ o) <= 512 /\ Forall (fun c => 0 <= c < 256) (d ++ o)
                /\ zlength o <= SN_CAP.
Proof.
  intros fmt kinds args Hin FA.
  pose proof lept_fmts_checked as CK. rewrite forallb_forall in CK. specialize (CK _ Hin).
  unfold fmt_check in CK. cbn [fst snd] in CK. apply andb_prop in CK. destruct CK as [P1 SBK].
  destruct (shape_bound (Datatypes.length fmt) fmt kinds) as [B|] eqn:SB; [|discriminate]. apply Z.leb_le in SBK.
  split; [exact P1|]. split; [exact (fp_shape _ _ _ _ _ SB FA)|].
  destruct (ppl_shape _ _ _ _ 0 _ SB FA ltac:(lia) ltac:(lia)) as (ps & r & P & Hr & Hz & Hby).
  destruct (printf_model_sn2 fmt args ps r P) as (d & o & RUN & FL & CAP).
  exists r, d, o. rewrite FL. repeat split; try assumption; lia.
Qed.

(* [comment removed for export] *)
Theorem lept_model_run_b : forall cap fmt kinds args,
  512 <= cap -> In (fmt, kinds) LEPT_FMT_LIST -> Forall2 lept_arg_ok kinds args ->
  pass1_ok fmt = true /\ fp_calls (Datatypes.length fmt) fmt args = [] /\
  exists r d o, printf_model (OUT_sn2b cap) OUTFP_sn2 fmt args ([], []) = ITree.Ret (Ok (r, (d, o)))
                /\ r = zlength (d ++ o) /\ zlength (d ++ o) <= 512 /\ Forall (fun c => 0 <= c < 256) (d ++ o)
                /\ zlength o <= SN_CAP.
Proof.
  intros cap fmt kinds args Hcap Hin FA.
  pose proof lept_fmts_checked as CK. rewrite forallb_forall in CK. specialize (CK _ Hin).
  unfold fmt_check in CK. cbn [fst snd] in CK. apply andb_prop in CK. destruct CK as [P1 SBK].
  destruct (shape_bound (Datatypes.length fmt) fmt kinds) as [B|] eqn:SB; [|discriminate]. apply Z.leb_le in SBK.
  split; [exact P1|]. split; [exact (fp_shape _ _ _ _ _ SB FA)|].
  destruct (ppl_shape _ _ _ _ 0 _ SB FA ltac:(lia) ltac:(lia)) as (ps & r & P & Hr & Hz & Hby).
  destruct (printf_model_sn2b cap fmt args ps r P ltac:(lia)) as (d & o & RUN & FL & CAP).
  exists r, d, o. rewrite FL. repeat split; try assumption; lia.
Qed.
