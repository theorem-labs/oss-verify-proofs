(** * SegPrintfBridge: DIS's printf model (CJ/RL/GX/Printf_model.v, the model every printf contract of this unit is
    stated over: snprintf_holds, snprintf_m_holds, vsnprintf_holds) computes exactly SegModel's [fmt] text and
    [snprintf_r] return value, for every format of the class [sp_ok] (literal bytes 1..255 except '%', and the
    conversions %s, %d, %u, %zu, %.NNs) and every argument list that fits it ([sp_fit]). All 23 formats segconf
    passes to snprintf / vsnprintf are in the class ([seg_formats_ok]); one corollary per format states the model
    equation at the argument types its call sites pass. No image, no machine: one file serves both builds. *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Lib Require Import ITree.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.Spec Require Import Prelim Monad FmtFp.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Import Printf_model.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.CJ.RL.GX Require Printf_text G_printf_core_common.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Spec Require SegModel.
Import G_printf_core_common.G_printf_iface.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(** ** 1. The class of formats and the arguments that fit them *)

(** [sp_ok f]: the format [f] (its bytes before the NUL) is made of literal bytes in 1..255 other than '%' and of
    the conversions %s, %d, %u, %zu and %.NNs (two decimal digits). *)
Fixpoint sp_ok (f : list Z) : bool :=
  match f with
  | [] => true
  | c :: f1 =>
    if c =? 37 then
      match f1 with
      | [] => false
      | c1 :: f2 =>
        if (c1 =? 115) || (c1 =? 100) || (c1 =? 117) then sp_ok f2
        else if c1 =? 122 then match f2 with [] => false | c2 :: f3 => (c2 =? 117) && sp_ok f3 end
        else if c1 =? 46 then
          match f2 with
          | d1 :: d2 :: c3 :: f4 => SegModel.isdigit d1 && SegModel.isdigit d2 && (c3 =? 115) && sp_ok f4
          | _ => false
          end
        else false
      end
    else (0 <? c) && (c <? 256) && sp_ok f1
  end.

(** The model's argument list for SegModel's [a] under [f]: a string conversion reads [arg_s] (the bytes before
    its NUL), %d an int, %u an unsigned int, %zu a size_t. *)
Fixpoint sp_pargs (f : list Z) (a : list SegModel.arg) : list parg :=
  match f with
  | [] => []
  | c :: f1 =>
    if c =? 37 then
      match f1 with
      | [] => []
      | c1 :: f2 =>
        match a with
        | [] => []
        | x :: a' =>
          if c1 =? 115 then PA_s (SegModel.arg_s x) :: sp_pargs f2 a'
          else if c1 =? 100 then PA_i (SegModel.arg_i x) :: sp_pargs f2 a'
          else if c1 =? 117 then PA_u (SegModel.arg_i x) :: sp_pargs f2 a'
          else if c1 =? 122 then match f2 with [] => [] | _ :: f3 => PA_ull (SegModel.arg_i x) :: sp_pargs f3 a' end
          else if c1 =? 46 then
            match f2 with _ :: _ :: _ :: f4 => PA_s (SegModel.arg_s x) :: sp_pargs f4 a' | _ => [] end
          else []
        end
      end
    else sp_pargs f1 a
  end.

(** [sp_fit f a]: every conversion of [f] has its argument, and each integer is in its C type's range. *)
Fixpoint sp_fit (f : list Z) (a : list SegModel.arg) : Prop :=
  match f with
  | [] => True
  | c :: f1 =>
    if c =? 37 then
      match f1 with
      | [] => True
      | c1 :: f2 =>
        match a with
        | [] => False
        | x :: a' =>
          if c1 =? 115 then sp_fit f2 a'
          else if c1 =? 100 then (-2^31 <= SegModel.arg_i x < 2^31) /\ sp_fit f2 a'
          else if c1 =? 117 then (0 <= SegModel.arg_i x < 2^32) /\ sp_fit f2 a'
          else if c1 =? 122 then match f2 with [] => True | _ :: f3 => (0 <= SegModel.arg_i x < 2^64) /\ sp_fit f3 a' end
          else if c1 =? 46 then match f2 with _ :: _ :: _ :: f4 => sp_fit f4 a' | _ => True end
          else True
        end
      end
    else sp_fit f1 a
  end.

(** ** 2. One step of each function *)

Lemma sp_ok_pct : forall c1 f2, sp_ok (37 :: c1 :: f2) =
  if (c1 =? 115) || (c1 =? 100) || (c1 =? 117) then sp_ok f2
  else if c1 =? 122 then match f2 with [] => false | c2 :: f3 => (c2 =? 117) && sp_ok f3 end
  else if c1 =? 46 then
    match f2 with
    | d1 :: d2 :: c3 :: f4 => SegModel.isdigit d1 && SegModel.isdigit d2 && (c3 =? 115) && sp_ok f4
    | _ => false
    end
  else false.
Proof. reflexivity. Qed.

Lemma sp_ok_lit : forall b r, b <> 37 -> sp_ok (b :: r) = (0 <? b) && (b <? 256) && sp_ok r.
Proof. intros b r Hb. cbn [sp_ok]. rewrite (proj2 (Z.eqb_neq b 37) Hb). reflexivity. Qed.
Lemma fmt_lit : forall b r a, b <> 37 -> SegModel.fmt (b :: r) a = b :: SegModel.fmt r a.
Proof. intros b r a Hb. cbn [SegModel.fmt]. rewrite (proj2 (Z.eqb_neq b 37) Hb). reflexivity. Qed.
Lemma pargs_lit : forall b r a, b <> 37 -> sp_pargs (b :: r) a = sp_pargs r a.
Proof. intros b r a Hb. cbn [sp_pargs]. rewrite (proj2 (Z.eqb_neq b 37) Hb). reflexivity. Qed.
Lemma fit_lit : forall b r a, b <> 37 -> sp_fit (b :: r) a = sp_fit r a.
Proof. intros b r a Hb. cbn [sp_fit]. rewrite (proj2 (Z.eqb_neq b 37) Hb). reflexivity. Qed.
Lemma fit_pct_nil : forall c1 f2, sp_fit (37 :: c1 :: f2) [] = False.
Proof. reflexivity. Qed.

(** ** 3. Decimal texts: SegModel's [dec] is the model's (Printf_text's) digit text *)

Lemma dec_go_pf : forall f n acc, 0 <= n -> SegModel.dec_go f n acc = Printf_text.pf_digits f n acc.
Proof.
  induction f as [|f IH]; intros n acc Hn; [reflexivity|].
  cbn [SegModel.dec_go Printf_text.pf_digits].
  destruct (Z.ltb_spec n 10) as [H|H].
  - rewrite Z.mod_small by lia. reflexivity.
  - apply IH. apply Z.div_pos; lia.
Qed.

Lemma dec_udec : forall u, 0 <= u -> SegModel.dec u = Printf_text.pf_udec u.
Proof.
  intros u Hu. unfold SegModel.dec, Printf_text.pf_udec.
  replace (u <? 0) with false by (symmetry; apply Z.ltb_ge; lia). apply dec_go_pf. lia.
Qed.

Lemma dec_pf_dec : forall v, -2^31 <= v < 2^31 -> SegModel.dec v = Printf_text.pf_dec v.
Proof.
  intros v Hv. unfold SegModel.dec, Printf_text.pf_dec.
  destruct (Z.ltb_spec v 0) as [Hn|Hn].
  - f_equal. rewrite dec_go_pf by lia. rewrite (Printf_text.pt_dec_eq (- v)) by lia.
    rewrite <- (Printf_text.pt_udec_eq (- v)) by lia. reflexivity.
  - destruct (Z.eq_dec v 0) as [->|Hz]; [reflexivity|].
    rewrite dec_go_pf by lia. rewrite (Printf_text.pt_dec_eq v) by lia.
    rewrite <- (Printf_text.pt_udec_eq v) by lia. reflexivity.
Qed.

(** ** 4. The literal precision %.NNs *)

Lemma pd_prec : forall d1 d2 t, SegModel.isdigit d1 = true -> SegModel.isdigit d2 = true ->
  parse_dir (46 :: d1 :: d2 :: 115 :: t) = Some (mkDir 0 0 ((d1 - 48) * 10 + (d2 - 48)) true 115 T_PTR, t).
Proof.
  intros d1 d2 t H1 H2. unfold SegModel.isdigit in H1, H2.
  rewrite andb_true_iff, !Z.leb_le in H1, H2.
  assert (E1 : exists i, d1 = 48 + Z.of_nat i /\ (i < 10)%nat) by (exists (Z.to_nat (d1 - 48)); lia).
  assert (E2 : exists j, d2 = 48 + Z.of_nat j /\ (j < 10)%nat) by (exists (Z.to_nat (d2 - 48)); lia).
  destruct E1 as [i [-> Hi]]. destruct E2 as [j [-> Hj]]. clear H1 H2.
  do 10 (destruct i as [|i]; [do 10 (destruct j as [|j]; [reflexivity|]); lia|]). lia.
Qed.

Lemma conv_prec_s : forall cnt k s, 0 <= k -> 0 <= cnt -> cnt + zlength (firstn (Z.to_nat k) s) <= INT_MAX ->
  exists ps, conv_pieces cnt (mkDir 0 0 k true 115 T_PTR) (PA_s s) = Some (ps, cnt + zlength (firstn (Z.to_nat k) s))
    /\ concat ps = firstn (Z.to_nat k) s.
Proof.
  intros cnt k s Hk Hc Hm.
  assert (E : firstn (Z.to_nat k) s = firstn (Z.to_nat (Z.min (zlength s) k)) s).
  { unfold zlength. destruct (Z.le_ge_cases k (Z.of_nat (length s))) as [H|H].
    - rewrite Z.min_r by lia. reflexivity.
    - rewrite Z.min_l by lia. rewrite Nat2Z.id. rewrite !firstn_all2 by lia. reflexivity. }
  assert (C : conv_pieces cnt (mkDir 0 0 k true 115 T_PTR) (PA_s s)
              = tail_pieces cnt 0 0 (Z.min (zlength s) k) [] (firstn (Z.to_nat (Z.min (zlength s) k)) s)).
  { unfold conv_pieces. cbv zeta. cbn [d_fl d_w d_p d_xp d_t d_ty].
    replace (k <? 0) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
  assert (L : zlength (firstn (Z.to_nat (Z.min (zlength s) k)) s) = Z.min (zlength s) k)
    by (unfold zlength in *; rewrite length_firstn; lia).
  rewrite C, E in *. rewrite L in *.
  pose proof (Printf_text.pt_zlength_nonneg s).
  apply Printf_text.pt_tail_exact.
  - change (zlength (@nil Z)) with 0. lia.
  - lia.
  - exact Hc.
  - change (zlength (@nil Z)) with 0. lia.
  - change (zlength (@nil Z)) with 0. lia.
  - reflexivity.
Qed.

(** ** 5. The literal run of a format of the class *)

Lemma sp_lit_split : forall f, sp_ok f = true ->
  exists L R, f = L ++ R /\ lit_run (f ++ [0]) = L /\ sp_ok R = true
    /\ (R = [] \/ exists c1 R', R = 37 :: c1 :: R' /\ c1 <> 37)
    /\ (forall a, SegModel.fmt f a = L ++ SegModel.fmt R a) /\ (forall a, sp_pargs f a = sp_pargs R a)
    /\ (forall a, sp_fit f a = sp_fit R a).
Proof.
  induction f as [|b r IH]; intros Hok.
  - exists [], []. repeat split; auto.
  - destruct (Z.eqb_spec b 37) as [->|Hb].
    + exists [], (37 :: r). split; [reflexivity|]. split; [reflexivity|]. split; [exact Hok|].
      split; [|repeat split; auto].
      right. destruct r as [|c1 f2]; [vm_compute in Hok; discriminate Hok|]. exists c1, f2. split; [reflexivity|].
      intros ->. rewrite sp_ok_pct in Hok. vm_compute in Hok. discriminate Hok.
    + rewrite sp_ok_lit in Hok by exact Hb. apply andb_prop in Hok as [Hb2 Hr].
      apply andb_prop in Hb2 as [Hb0 _]. apply Z.ltb_lt in Hb0.
      destruct (IH Hr) as (L & R & E & HL & HR & HRf & Hf & Hp & Hs).
      exists (b :: L), R. split; [cbn [app]; rewrite E; reflexivity|].
      split.
      { cbn [app lit_run]. replace ((b =? 0) || (b =? 37)) with false
          by (symmetry; apply orb_false_iff; split; apply Z.eqb_neq; lia).
        rewrite HL. reflexivity. }
      split; [exact HR|]. split; [exact HRf|].
      split; [intros a; rewrite fmt_lit by exact Hb; rewrite Hf; reflexivity|].
      split; [intros a; rewrite pargs_lit by exact Hb; apply Hp|].
      intros a; rewrite fit_lit by exact Hb; apply Hs.
Qed.

(** ** 6. The theorem: the model's pieces of [f ++ [0]] concatenate to [fmt f a], and their count is its length *)

Lemma sp_loop : forall fuel f a cnt,
  (length f < fuel)%nat -> sp_ok f = true -> sp_fit f a -> 0 <= cnt ->
  cnt + zlength (SegModel.fmt f a) < INT_MAX ->
  exists ps, printf_pieces_loop fuel (f ++ [0]) (sp_pargs f a) cnt = Some (ps, cnt + zlength (SegModel.fmt f a))
    /\ concat ps = SegModel.fmt f a.
Proof.
  induction fuel as [|fuel IH]; intros f a cnt Hlen Hok Hfit Hc HT; [lia|].
  destruct f as [|b r].
  { exists []. split; [|reflexivity]. change (zlength (SegModel.fmt [] a)) with 0. rewrite Z.add_0_r. reflexivity. }
  destruct (Z.eqb_spec b 37) as [->|Hb].
  - (* a conversion *)
    destruct r as [|c1 f2]; [vm_compute in Hok; discriminate Hok|]. cbn [length] in Hlen.
    destruct a as [|x a']; [rewrite fit_pct_nil in Hfit; destruct Hfit|].
    destruct (Z.eqb_spec c1 115) as [->|N1].
    { (* %s *)
      change (sp_ok f2 = true) in Hok. change (sp_fit f2 a') in Hfit.
      change (SegModel.fmt (37 :: 115 :: f2) (x :: a')) with (SegModel.arg_s x ++ SegModel.fmt f2 a') in *.
      change (sp_pargs (37 :: 115 :: f2) (x :: a')) with (PA_s (SegModel.arg_s x) :: sp_pargs f2 a').
      rewrite Printf_text.pt_zlength_app in HT.
      pose proof (Printf_text.pt_zlength_nonneg (SegModel.arg_s x)).
      pose proof (Printf_text.pt_zlength_nonneg (SegModel.fmt f2 a')).
      destruct (Printf_text.pt_conv_s cnt (SegModel.arg_s x) ltac:(lia) Hc ltac:(lia)) as (ps1 & C & E1).
      destruct (IH f2 a' (cnt + zlength (SegModel.arg_s x)) ltac:(lia) Hok Hfit ltac:(lia) ltac:(lia))
        as (pcs & P & E).
      exact (Printf_text.pt_dir_glue fuel 115 (f2 ++ [0]) _ _ _ _ cnt ps1 (SegModel.arg_s x) pcs (SegModel.fmt f2 a')
               ltac:(lia) (Printf_text.pt_pd_s _) C E1 P E). }
    destruct (Z.eqb_spec c1 100) as [->|N2].
    { (* %d *)
      change (sp_ok f2 = true) in Hok.
      change ((-2^31 <= SegModel.arg_i x < 2^31) /\ sp_fit f2 a') in Hfit. destruct Hfit as [Hv Hfit].
      change (SegModel.fmt (37 :: 100 :: f2) (x :: a'))
        with (SegModel.dec (SegModel.arg_i x) ++ SegModel.fmt f2 a') in *.
      change (sp_pargs (37 :: 100 :: f2) (x :: a')) with (PA_i (SegModel.arg_i x) :: sp_pargs f2 a').
      rewrite (dec_pf_dec _ Hv) in *.
      rewrite Printf_text.pt_zlength_app in HT.
      pose proof (Printf_text.pt_zlength_nonneg (Printf_text.pf_dec (SegModel.arg_i x))).
      pose proof (Printf_text.pt_zlength_nonneg (SegModel.fmt f2 a')).
      destruct (Printf_text.pt_conv_d cnt (SegModel.arg_i x) Hv Hc ltac:(lia)) as (ps1 & C & E1).
      destruct (IH f2 a' (cnt + zlength (Printf_text.pf_dec (SegModel.arg_i x))) ltac:(lia) Hok Hfit ltac:(lia)
                  ltac:(lia)) as (pcs & P & E).
      exact (Printf_text.pt_dir_glue fuel 100 (f2 ++ [0]) _ _ _ _ cnt ps1 _ pcs (SegModel.fmt f2 a')
               ltac:(lia) (Printf_text.pt_pd_d _) C E1 P E). }
    destruct (Z.eqb_spec c1 117) as [->|N3].
    { (* %u *)
      change (sp_ok f2 = true) in Hok.
      change ((0 <= SegModel.arg_i x < 2^32) /\ sp_fit f2 a') in Hfit. destruct Hfit as [Hv Hfit].
      change (SegModel.fmt (37 :: 117 :: f2) (x :: a'))
        with (SegModel.dec (SegModel.arg_i x) ++ SegModel.fmt f2 a') in *.
      change (sp_pargs (37 :: 117 :: f2) (x :: a')) with (PA_u (SegModel.arg_i x) :: sp_pargs f2 a').
      rewrite (dec_udec (SegModel.arg_i x) ltac:(lia)) in *.
      rewrite Printf_text.pt_zlength_app in HT.
      pose proof (Printf_text.pt_zlength_nonneg (Printf_text.pf_udec (SegModel.arg_i x))).
      pose proof (Printf_text.pt_zlength_nonneg (SegModel.fmt f2 a')).
      destruct (Printf_text.pt_conv_u cnt (SegModel.arg_i x) ltac:(lia) Hc ltac:(lia)) as (ps1 & C & E1).
      destruct (IH f2 a' (cnt + zlength (Printf_text.pf_udec (SegModel.arg_i x))) ltac:(lia) Hok Hfit ltac:(lia)
                  ltac:(lia)) as (pcs & P & E).
      exact (Printf_text.pt_dir_glue fuel 117 (f2 ++ [0]) _ _ _ _ cnt ps1 _ pcs (SegModel.fmt f2 a')
               ltac:(lia) (Printf_text.pt_pd_u _) C E1 P E). }
    destruct (Z.eqb_spec c1 122) as [->|N4].
    { (* %zu *)
      destruct f2 as [|c2 f3]; [vm_compute in Hok; discriminate Hok|].
      change ((c2 =? 117) && sp_ok f3 = true) in Hok. apply andb_prop in Hok as [H117 Hok].
      apply Z.eqb_eq in H117. subst c2. cbn [length] in Hlen.
      change ((0 <= SegModel.arg_i x < 2^64) /\ sp_fit f3 a') in Hfit. destruct Hfit as [Hv Hfit].
      change (SegModel.fmt (37 :: 122 :: 117 :: f3) (x :: a'))
        with (SegModel.dec (SegModel.arg_i x) ++ SegModel.fmt f3 a') in *.
      change (sp_pargs (37 :: 122 :: 117 :: f3) (x :: a')) with (PA_ull (SegModel.arg_i x) :: sp_pargs f3 a').
      rewrite (dec_udec (SegModel.arg_i x) ltac:(lia)) in *.
      rewrite Printf_text.pt_zlength_app in HT.
      pose proof (Printf_text.pt_zlength_nonneg (Printf_text.pf_udec (SegModel.arg_i x))).
      pose proof (Printf_text.pt_zlength_nonneg (SegModel.fmt f3 a')).
      destruct (Printf_text.pt_conv_ull cnt T_SIZET (SegModel.arg_i x) (or_intror eq_refl) ltac:(lia) Hc ltac:(lia))
        as (ps1 & C & E1).
      destruct (IH f3 a' (cnt + zlength (Printf_text.pf_udec (SegModel.arg_i x))) ltac:(lia) Hok Hfit ltac:(lia)
                  ltac:(lia)) as (pcs & P & E).
      exact (Printf_text.pt_dir_glue fuel 122 (117 :: (f3 ++ [0])) _ _ _ _ cnt ps1 _ pcs (SegModel.fmt f3 a')
               ltac:(lia) (Printf_text.pt_pd_zu _) C E1 P E). }
    destruct (Z.eqb_spec c1 46) as [->|N5].
    { (* %.NNs *)
      destruct f2 as [|d1 [|d2 [|c3 f4]]]; try (vm_compute in Hok; discriminate Hok).
      change (SegModel.isdigit d1 && SegModel.isdigit d2 && (c3 =? 115) && sp_ok f4 = true) in Hok.
      apply andb_prop in Hok as [Hok Hf4]. apply andb_prop in Hok as [Hok H115]. apply andb_prop in Hok as [Hd1 Hd2].
      apply Z.eqb_eq in H115. subst c3. cbn [length] in Hlen.
      change (sp_fit f4 a') in Hfit.
      assert (EF : SegModel.fmt (37 :: 46 :: d1 :: d2 :: 115 :: f4) (x :: a')
                   = firstn (Z.to_nat ((d1 - 48) * 10 + (d2 - 48))) (SegModel.arg_s x) ++ SegModel.fmt f4 a').
      { change (SegModel.fmt (37 :: 46 :: d1 :: d2 :: 115 :: f4) (x :: a'))
          with (if SegModel.isdigit d1 && SegModel.isdigit d2 && (115 =? 115)
                then firstn (Z.to_nat ((d1 - 48) * 10 + (d2 - 48))) (SegModel.arg_s x) ++ SegModel.fmt f4 a'
                else []).
        rewrite Hd1, Hd2. reflexivity. }
      rewrite EF in *.
      change (sp_pargs (37 :: 46 :: d1 :: d2 :: 115 :: f4) (x :: a')) with (PA_s (SegModel.arg_s x) :: sp_pargs f4 a').
      assert (Hk : 0 <= (d1 - 48) * 10 + (d2 - 48)).
      { unfold SegModel.isdigit in Hd1, Hd2. rewrite andb_true_iff, !Z.leb_le in Hd1, Hd2. lia. }
      set (k := (d1 - 48) * 10 + (d2 - 48)) in *.
      set (X := firstn (Z.to_nat k) (SegModel.arg_s x)) in *.
      rewrite Printf_text.pt_zlength_app in HT.
      pose proof (Printf_text.pt_zlength_nonneg X). pose proof (Printf_text.pt_zlength_nonneg (SegModel.fmt f4 a')).
      destruct (conv_prec_s cnt k (SegModel.arg_s x) Hk Hc ltac:(subst X; lia)) as (ps1 & C & E1).
      destruct (IH f4 a' (cnt + zlength X) ltac:(lia) Hf4 Hfit ltac:(lia) ltac:(lia)) as (pcs & P & E).
      exact (Printf_text.pt_dir_glue fuel 46 (d1 :: d2 :: 115 :: (f4 ++ [0])) _ (f4 ++ [0]) _ _ cnt ps1 X pcs
               (SegModel.fmt f4 a') ltac:(lia) (pd_prec d1 d2 (f4 ++ [0]) Hd1 Hd2) C E1 P E). }
    exfalso. rewrite sp_ok_pct in Hok.
    rewrite (proj2 (Z.eqb_neq _ _) N1), (proj2 (Z.eqb_neq _ _) N2), (proj2 (Z.eqb_neq _ _) N3),
            (proj2 (Z.eqb_neq _ _) N4), (proj2 (Z.eqb_neq _ _) N5) in Hok.
    vm_compute in Hok. discriminate Hok.
  - (* a literal run *)
    destruct (sp_lit_split (b :: r) Hok) as (L & R & EL & HL & HR & HRf & Hf & Hp & Hs).
    rewrite sp_ok_lit in Hok by exact Hb. apply andb_prop in Hok as [Hb2 _].
    apply andb_prop in Hb2 as [Hb0 _]. apply Z.ltb_lt in Hb0.
    assert (HL0 : 0 < zlength L).
    { destruct L as [|y L]; [|unfold zlength; cbn [length]; lia].
      cbn [app] in EL. destruct HRf as [->|(c1 & R' & -> & _)]; [discriminate EL|].
      injection EL as EL _. contradiction. }
    assert (HlenR : (length R < fuel)%nat).
    { rewrite EL, length_app in Hlen. unfold zlength in HL0. lia. }
    rewrite Hf, Printf_text.pt_zlength_app in HT. rewrite Hs in Hfit.
    pose proof (Printf_text.pt_zlength_nonneg (SegModel.fmt R a)).
    destruct (IH R a (cnt + zlength L) HlenR HR Hfit ltac:(lia) ltac:(lia)) as (pcs & P & E).
    exists (L :: pcs). rewrite Hf, Hp. split.
    + rewrite Printf_text.pt_zlength_app, Z.add_assoc. change ((b :: r) ++ [0]) with (b :: (r ++ [0])).
      eapply Printf_text.pt_lit_step with (s1 := R ++ [0]); [lia | exact HL | | exact HL0 | | lia | exact P].
      * change (b :: r ++ [0]) with ((b :: r) ++ [0]). rewrite EL, <- app_assoc. apply Printf_text.pt_skipn_app.
      * destruct HRf as [->|(c1 & R' & -> & Hc1)]; [left; reflexivity|].
        right. split; [reflexivity|]. exists c1, (R' ++ [0]). split; [reflexivity|exact Hc1].
    + cbn [concat]. rewrite E. reflexivity.
Qed.

Theorem seg_printf_pieces : forall f a, sp_ok f = true -> sp_fit f a -> zlength (SegModel.fmt f a) < INT_MAX ->
  exists ps, printf_pieces (f ++ [0]) (sp_pargs f a) = Some (ps, zlength (SegModel.fmt f a))
    /\ concat ps = SegModel.fmt f a.
Proof.
  intros f a Hok Hfit HL.
  destruct (sp_loop (length (f ++ [0])) f a 0 ltac:(rewrite length_app; cbn [length]; lia) Hok Hfit
              ltac:(lia) ltac:(lia)) as (ps & P & E).
  exists ps. split; [exact P | exact E].
Qed.

(** The model equation in the form the printf contracts take it (snprintf_m_contract, vsnprintf_contract): the
    model's text is SegModel's [fmt f a] and its value SegModel's [snprintf_r f a]; the bytes stored before the NUL,
    [firstn (n - 1) o], are SegModel's [snprintf_s n f a] ([snprintf_s_firstn]). *)
Theorem seg_printf_model : forall f a, sp_ok f = true -> sp_fit f a -> zlength (SegModel.fmt f a) < INT_MAX ->
  printf_model (St:=list Z) (OUT_snf (zlength (SegModel.fmt f a))) OUTFP_snf (f ++ [0]) (sp_pargs f a) []
    = ITree.Ret (Ok (SegModel.snprintf_r f a, SegModel.fmt f a)).
Proof.
  intros f a Hok Hfit HL. destruct (seg_printf_pieces f a Hok Hfit HL) as (ps & P & E).
  pose proof (Printf_text.printf_model_snf_pieces (zlength (SegModel.fmt f a)) _ _ ps _ P ltac:(rewrite E; lia)) as M.
  rewrite E in M. exact M.
Qed.

Lemma snprintf_s_firstn : forall n f a, firstn (Z.to_nat (n - 1)) (SegModel.fmt f a) = SegModel.snprintf_s n f a.
Proof. reflexivity. Qed.

(** ** 7. The 23 formats segconf passes (SegModel's names) are in the class, pass the
    model's first-directive check, and are bytes. *)
Definition SEG_FORMATS : list (list Z) :=
  [SegModel.F_s; SegModel.F_ss; SegModel.F_addr_line; SegModel.F_addr; SegModel.F_label; SegModel.F_probe;
   SegModel.F_long; SegModel.F_notclosed; SegModel.F_after; SegModel.F_unknown; SegModel.F_noname;
   SegModel.F_toolong; SegModel.F_bound; SegModel.F_twice; SegModel.F_neither; SegModel.F_outside;
   SegModel.F_badrole; SegModel.F_badmodel; SegModel.F_badignore; SegModel.F_knock; SegModel.F_nokey;
   SegModel.F_xmodel; SegModel.F_xbox].

Definition fmt_good (f : list Z) : bool :=
  sp_ok f && pass1_ok (f ++ [0]) && forallb (fun c => (0 <=? c) && (c <? 256)) f.

Lemma seg_formats_ok : forallb fmt_good SEG_FORMATS = true.
Proof. vm_compute. reflexivity. Qed.

Lemma fmt_good_ok : forall f, fmt_good f = true ->
  sp_ok f = true /\ pass1_ok (f ++ [0]) = true /\ Forall (fun c => 0 <= c < 256) f.
Proof.
  intros f H. unfold fmt_good in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  split; [exact H1|]. split; [exact H2|].
  apply Forall_forall. intros c Hc. rewrite forallb_forall in H3. specialize (H3 c Hc).
  apply andb_prop in H3 as [Ha Hb]. apply Z.leb_le in Ha. apply Z.ltb_lt in Hb. lia.
Qed.

Lemma seg_format_good : forall f, In f SEG_FORMATS ->
  sp_ok f = true /\ pass1_ok (f ++ [0]) = true /\ Forall (fun c => 0 <= c < 256) f.
Proof.
  intros f Hin. apply fmt_good_ok. pose proof seg_formats_ok as H. rewrite forallb_forall in H. exact (H f Hin).
Qed.

(** ** 8. One model equation per format, at the argument types its call sites pass (strings are [AS s], read up
    to their NUL; integers [AI z] in the C type's range). *)
(** [pm_eq f a]: the model equation of [seg_printf_model] at [f] and [a]. *)
Definition pm_eq (f : list Z) (a : list SegModel.arg) : Prop :=
  printf_model (St:=list Z) (OUT_snf (zlength (SegModel.fmt f a))) OUTFP_snf (f ++ [0]) (sp_pargs f a) []
    = ITree.Ret (Ok (SegModel.snprintf_r f a, SegModel.fmt f a)).

(** [sp_fit] of a concrete format: its bytes first become a literal list (vm_compute; the strings of SegModel are
    [sb] texts), then [sp_fit] unrolls over it. *)
Ltac fit_tac :=
  match goal with |- sp_fit ?F _ =>
    let v := eval vm_compute in F in
    replace F with v by (vm_compute; reflexivity)
  end;
  cbn [sp_fit Z.eqb Pos.eqb SegModel.arg_i]; repeat split; lia.

Ltac seg_pm :=
  intros; unfold pm_eq; apply seg_printf_model; [ vm_compute; reflexivity | fit_tac | assumption ].

Lemma pm_s : forall s, zlength (SegModel.fmt SegModel.F_s [SegModel.AS s]) < INT_MAX ->
  pm_eq SegModel.F_s [SegModel.AS s].
Proof. seg_pm. Qed.
Lemma pm_ss : forall s1 s2, zlength (SegModel.fmt SegModel.F_ss [SegModel.AS s1; SegModel.AS s2]) < INT_MAX ->
  pm_eq SegModel.F_ss [SegModel.AS s1; SegModel.AS s2].
Proof. seg_pm. Qed.
Lemma pm_addr_line : forall r line, -2^31 <= line < 2^31 ->
  zlength (SegModel.fmt SegModel.F_addr_line [SegModel.AS r; SegModel.AI line]) < INT_MAX ->
  pm_eq SegModel.F_addr_line [SegModel.AS r; SegModel.AI line].
Proof. seg_pm. Qed.
Lemma pm_addr : forall r, zlength (SegModel.fmt SegModel.F_addr [SegModel.AS r]) < INT_MAX ->
  pm_eq SegModel.F_addr [SegModel.AS r].
Proof. seg_pm. Qed.
Lemma pm_label : forall lb, 0 <= lb < 2^32 ->
  zlength (SegModel.fmt SegModel.F_label [SegModel.AI lb]) < INT_MAX -> pm_eq SegModel.F_label [SegModel.AI lb].
Proof. seg_pm. Qed.
Lemma pm_probe : forall s, zlength (SegModel.fmt SegModel.F_probe [SegModel.AS s]) < INT_MAX ->
  pm_eq SegModel.F_probe [SegModel.AS s].
Proof. seg_pm. Qed.
Lemma pm_long : forall z, 0 <= z < 2^64 ->
  zlength (SegModel.fmt SegModel.F_long [SegModel.AI z]) < INT_MAX -> pm_eq SegModel.F_long [SegModel.AI z].
Proof. seg_pm. Qed.
Lemma pm_notclosed : forall s, zlength (SegModel.fmt SegModel.F_notclosed [SegModel.AS s]) < INT_MAX ->
  pm_eq SegModel.F_notclosed [SegModel.AS s].
Proof. seg_pm. Qed.
Lemma pm_after : forall s, zlength (SegModel.fmt SegModel.F_after [SegModel.AS s]) < INT_MAX ->
  pm_eq SegModel.F_after [SegModel.AS s].
Proof. seg_pm. Qed.
Lemma pm_unknown : forall s, zlength (SegModel.fmt SegModel.F_unknown [SegModel.AS s]) < INT_MAX ->
  pm_eq SegModel.F_unknown [SegModel.AS s].
Proof. seg_pm. Qed.
Lemma pm_noname : zlength (SegModel.fmt SegModel.F_noname []) < INT_MAX -> pm_eq SegModel.F_noname [].
Proof. seg_pm. Qed.
Lemma pm_toolong : forall s z, -2^31 <= z < 2^31 ->
  zlength (SegModel.fmt SegModel.F_toolong [SegModel.AS s; SegModel.AI z]) < INT_MAX ->
  pm_eq SegModel.F_toolong [SegModel.AS s; SegModel.AI z].
Proof. seg_pm. Qed.
Lemma pm_bound : forall s z, -2^31 <= z < 2^31 ->
  zlength (SegModel.fmt SegModel.F_bound [SegModel.AS s; SegModel.AI z]) < INT_MAX ->
  pm_eq SegModel.F_bound [SegModel.AS s; SegModel.AI z].
Proof. seg_pm. Qed.
Lemma pm_twice : forall s, zlength (SegModel.fmt SegModel.F_twice [SegModel.AS s]) < INT_MAX ->
  pm_eq SegModel.F_twice [SegModel.AS s].
Proof. seg_pm. Qed.
Lemma pm_neither : forall s, zlength (SegModel.fmt SegModel.F_neither [SegModel.AS s]) < INT_MAX ->
  pm_eq SegModel.F_neither [SegModel.AS s].
Proof. seg_pm. Qed.
Lemma pm_outside : forall s, zlength (SegModel.fmt SegModel.F_outside [SegModel.AS s]) < INT_MAX ->
  pm_eq SegModel.F_outside [SegModel.AS s].
Proof. seg_pm. Qed.
Lemma pm_badrole : forall s1 s2, zlength (SegModel.fmt SegModel.F_badrole [SegModel.AS s1; SegModel.AS s2]) < INT_MAX ->
  pm_eq SegModel.F_badrole [SegModel.AS s1; SegModel.AS s2].
Proof. seg_pm. Qed.
Lemma pm_badmodel : forall s1 s2 s3,
  zlength (SegModel.fmt SegModel.F_badmodel [SegModel.AS s1; SegModel.AS s2; SegModel.AS s3]) < INT_MAX ->
  pm_eq SegModel.F_badmodel [SegModel.AS s1; SegModel.AS s2; SegModel.AS s3].
Proof. seg_pm. Qed.
Lemma pm_badignore : forall s1 s2,
  zlength (SegModel.fmt SegModel.F_badignore [SegModel.AS s1; SegModel.AS s2]) < INT_MAX ->
  pm_eq SegModel.F_badignore [SegModel.AS s1; SegModel.AS s2].
Proof. seg_pm. Qed.
Lemma pm_knock : forall s1 s2, zlength (SegModel.fmt SegModel.F_knock [SegModel.AS s1; SegModel.AS s2]) < INT_MAX ->
  pm_eq SegModel.F_knock [SegModel.AS s1; SegModel.AS s2].
Proof. seg_pm. Qed.
Lemma pm_nokey : forall s1 s2, zlength (SegModel.fmt SegModel.F_nokey [SegModel.AS s1; SegModel.AS s2]) < INT_MAX ->
  pm_eq SegModel.F_nokey [SegModel.AS s1; SegModel.AS s2].
Proof. seg_pm. Qed.
Lemma pm_xmodel : forall s1 s2, zlength (SegModel.fmt SegModel.F_xmodel [SegModel.AS s1; SegModel.AS s2]) < INT_MAX ->
  pm_eq SegModel.F_xmodel [SegModel.AS s1; SegModel.AS s2].
Proof. seg_pm. Qed.
Lemma pm_xbox : forall s, zlength (SegModel.fmt SegModel.F_xbox [SegModel.AS s]) < INT_MAX ->
  pm_eq SegModel.F_xbox [SegModel.AS s].
Proof. seg_pm. Qed.

(** The model's argument lists of the call sites, as the contracts' [pm_args_ok] reads them. *)
Lemma pargs_knock : forall s1 s2,
  sp_pargs SegModel.F_knock [SegModel.AS s1; SegModel.AS s2] = [PA_s (SegModel.cut_nul s1); PA_s (SegModel.cut_nul s2)].
Proof. vm_compute. reflexivity. Qed.
Lemma pargs_long : forall z, sp_pargs SegModel.F_long [SegModel.AI z] = [PA_ull z].
Proof. vm_compute. reflexivity. Qed.
Lemma pargs_label : forall lb, sp_pargs SegModel.F_label [SegModel.AI lb] = [PA_u lb].
Proof. vm_compute. reflexivity. Qed.
Lemma pargs_addr_line : forall r line,
  sp_pargs SegModel.F_addr_line [SegModel.AS r; SegModel.AI line] = [PA_s (SegModel.cut_nul r); PA_i line].
Proof. vm_compute. reflexivity. Qed.

(** ** 9. Satisfiability witness: the knock refusal after the address prefix "%s:%d: ", at a 95-byte label (the most the
    96-byte reading holds), line 65535, a 15-byte name and a 30-byte value. refuse writes the prefix (k bytes, its
    snprintf return) into the 200-byte slot and vsnprintf's text into the 200 - k bytes after it; "takes no plan"
    lies at bytes 135..147 of the slot, before byte 199. *)
Definition W_label : list Z := repeat 97 95.
Definition W_line : Z := 65535.
Definition W_name : list Z := repeat 110 15.
Definition W_val : list Z := repeat 118 30.
Definition W_pre_args : list SegModel.arg := [SegModel.AS W_label; SegModel.AI W_line].
Definition W_knock_args : list SegModel.arg := [SegModel.AS W_name; SegModel.AS W_val].
Definition W_k : Z := SegModel.snprintf_r SegModel.F_addr_line W_pre_args.
Definition W_slot : list Z :=
  SegModel.snprintf_s 200 SegModel.F_addr_line W_pre_args ++ SegModel.snprintf_s (200 - W_k) SegModel.F_knock W_knock_args.

Lemma t06_prefix_model : pm_eq SegModel.F_addr_line W_pre_args.
Proof. unfold W_pre_args. apply pm_addr_line; [unfold W_line; lia | vm_compute; reflexivity]. Qed.
Lemma t06_knock_model : pm_eq SegModel.F_knock W_knock_args.
Proof. unfold W_knock_args. apply pm_knock. vm_compute. reflexivity. Qed.

(** The slot holds the 103-byte prefix and then 96 bytes of the knock text (vsnprintf's n = 200 - 103 = 97): 199
    bytes before the NUL; "takes no plan" is bytes 135..147 (103 + "[segment " 9 + the name 15 + "] knock " 8). *)
Theorem t06_witness :
  W_k = 103 /\ length W_slot = 199%nat
  /\ firstn 13 (skipn 135 W_slot) = SegModel.TNP /\ Nat.leb (135 + 13) 199 = true.
Proof. vm_compute. repeat split; reflexivity. Qed.
