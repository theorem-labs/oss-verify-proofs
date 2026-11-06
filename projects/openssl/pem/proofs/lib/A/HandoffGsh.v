(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Monad Specs Run Fs.
From OSSVerify.Proofs.openssl.pem.lib.Common Require Import PropExec AgentLib AsanAcct AxSymExec3 AxSymExec3Sound AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.pem.lib.Start Require Import AsanRegModel AsanGshModel.
From OSSVerify.Proofs.openssl.pem.lib.A Require Import HandoffKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import AP.
Open Scope Z_scope.

Module HGSH.
Import RGM.

Section Checks.
Variable T : ctab.
Variable TAB : list desc.
Variable HULLS : list (Z * Z).
#[local] Notation y := (c_lay T) (only parsing).
Definition tlo : Z := shad y (c_tab T).
Definition thi : Z := shad y (c_tabend T).

(* [comment removed for export] *)
Definition apart_tab (lo hi : Z) : bool := (hi <=? tlo) || (thi <=? lo).
(* [comment removed for export] *)
Definition zero_okb (lo hi : Z) : bool :=
  apart_tab lo hi && forallb (fun d => (GSM.wr_hi y d <=? lo) || (hi <=? GSM.wr_lo y d)) TAB.
(* [comment removed for export] *)
Definition f9_okb (lo hi : Z) : bool :=
  if (tlo <=? lo) && (hi <=? thi) then true
  else if apart_tab lo hi
       then existsb (fun d => (GSM.wr_lo y d <=? lo) && (hi <=? GSM.wr_hi y d) && ((GSM.wr_lo y d <? lo) || (d_size d mod 8 =? 0))) TAB
       else false.
(* [comment removed for export] *)
Definition part_okb (lo c : Z) : bool :=
  apart_tab lo (lo + 1) && negb (c =? 0)
  && existsb (fun d => (lo =? GSM.wr_lo y d) && (c =? d_size d mod 8) && (GSM.wr_lo y d <? GSM.wr_hi y d)) TAB.
Definition const_okb (lo hi c : Z) : bool :=
  if c =? 0 then zero_okb lo hi else if c =? GSM.F9 then f9_okb lo hi else (hi =? lo + 1) && part_okb lo c.

(* [comment removed for export] *)
Definition piece_len (K : kentry) (pos : Z) : option Z :=
  (* [comment removed for export] *)
  match K with
  | KZero (SA (ELit 0) a) (ELit n) => if a =? pos then (if (0 <? n) && const_okb pos (pos + n) 0 then Some n else None) else None
  | KFill (SA (ELit 0) a) (ELit n) c =>
      if a =? pos then (if (0 <? n) && (0 <=? c) && (c <? 256) && const_okb pos (pos + n) c then Some n else None) else None
  | KWord (SA (ELit 0) a) 1%nat (ELit c) => if a =? pos then (if (0 <=? c) && (c <? 256) && const_okb pos (pos + 1) c then Some 1 else None) else None
  | KBlob (SA (ELit 0) a) (ELit n) k =>
      if a =? pos then
        (if (0 <? n) && Nat.leb K_GSH0 k && apart_tab pos (pos + n)
            && match nth_error HULLS (k - K_GSH0) with Some (lo, hi) => (lo =? pos) && (hi =? pos + n) | None => false end
         then Some n else None)
      else None
  | _ => None
  end.

Fixpoint find_piece (k : list kentry) (pos : Z) : option Z :=
  match k with
  | [] => None
  | K :: r => match piece_len K pos with Some n => Some n | None => find_piece r pos end
  end.

Fixpoint tile (fuel : nat) (k : list kentry) (pos hi : Z) : bool :=
  if pos =? hi then true else
  match fuel with
  | O => false
  | S f => match find_piece k pos with Some n => (pos + n <=? hi) && tile f k (pos + n) hi | None => false end
  end.

(* [comment removed for export] *)
Definition hs_gsh_ok (A : atable) (ch : acs) : bool :=
  let wlo := shad y (l_ilo y) in let whi := shad y (l_ihi y) in
  (img_hi A <=? wlo) && (0 <=? wlo) && (wlo <=? whi) && (whi <=? 2 ^ 47) && tile (length (kn ch)) (kn ch) wlo whi.

(* [comment removed for export] *)
Hypothesis HSORT : GSM.sortedb (l_ilo y) TAB = true.

Lemma apart_tab_gshw : forall lo hi x, apart_tab lo hi = true -> lo <= x < hi -> GSM.gshw T TAB x = GSM.gsh y TAB x.
Proof.
  intros lo hi x H Hx. unfold GSM.gshw. fold tlo thi. unfold apart_tab in H.
  destruct (Z.leb_spec tlo x), (Z.ltb_spec x thi); cbn [andb]; try reflexivity.
  apply orb_prop in H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma const_ok_sound : forall lo hi c x, const_okb lo hi c = true -> lo <= x < hi -> GSM.gshw T TAB x = c.
Proof.
  intros lo hi c x H Hx. unfold const_okb in H.
  destruct (Z.eqb_spec c 0) as [->|Nc0].
  - unfold zero_okb in H. apply andb_prop in H as [Ha Hf]. rewrite (apart_tab_gshw lo hi x Ha Hx).
    apply GSM.gsh_gap. intros d Hd. rewrite forallb_forall in Hf. specialize (Hf d Hd).
    apply orb_prop in Hf as [Y|Y]; apply Z.leb_le in Y; lia.
  - destruct (Z.eqb_spec c GSM.F9) as [->|Nf9].
    + unfold f9_okb in H. destruct ((tlo <=? lo) && (hi <=? thi)) eqn:Htab.
      * apply andb_prop in Htab as [H1 H2]. apply Z.leb_le in H1, H2. unfold GSM.gshw. fold tlo thi.
        assert (Y1 : tlo <= x) by lia. assert (Y2 : x < thi) by lia.
        rewrite (proj2 (Z.leb_le _ _) Y1), (proj2 (Z.ltb_lt _ _) Y2). reflexivity.
      * destruct (apart_tab lo hi) eqn:Ha; [|discriminate H]. rename H into He. rewrite (apart_tab_gshw lo hi x Ha Hx).
        apply existsb_exists in He as (d & Hd & Hc). apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2].
        apply Z.leb_le in C1, C2. apply (GSM.gsh_redzone y TAB (l_ilo y) d x HSORT Hd); [lia|].
        apply orb_prop in C3 as [C3|C3]; [left; apply Z.ltb_lt in C3; lia | right; apply Z.eqb_eq in C3; exact C3].
    + apply andb_prop in H as [Hh H]. apply Z.eqb_eq in Hh. unfold part_okb in H.
      apply andb_prop in H as [H He]. apply andb_prop in H as [Ha _].
      rewrite (apart_tab_gshw lo (lo + 1) x Ha ltac:(lia)).
      apply existsb_exists in He as (d & Hd & Hc). apply andb_prop in Hc as [Hc C3]. apply andb_prop in Hc as [C1 C2].
      apply Z.eqb_eq in C1, C2. apply Z.ltb_lt in C3. assert (x = GSM.wr_lo y d) by lia. subst x c.
      apply (GSM.gsh_partial y TAB (l_ilo y) d HSORT Hd); [exact Nc0 | exact C3].
Qed.

End Checks.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variables (SEGS : list Segment) (A : atable) (LIMIT : Z)
          (SINV : env -> (word -> option byte) -> Prop) (argH : env -> word -> bool) (ISP : Z) (FS0 : Fs.Fs).
Hypothesis SEGS_in_hull : forall a : word, APS.in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : APS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variables (E : env) (ch : acs) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis HC : APS.cs_ok SEGS A LIMIT SINV argH ISP FS0 E ch R FULL model.
Variable A' : list (Z * Z).
Hypothesis HA' : forall p, page_allowedb (APS.allowA A E ch) p = true -> page_allowedb A' p = true.
Variable T : ctab.
Variable TAB : list desc.
Variable HULLS : list (Z * Z).
#[local] Notation y := (c_lay T) (only parsing).
Hypothesis HSORT : GSM.sortedb (l_ilo y) TAB = true.
(* [comment removed for export] *)
Hypothesis HBL : forall j lo hi, nth_error HULLS j = Some (lo, hi) -> eb E (K_GSH0 + j)%nat = map (Z_to_bv 8) (GSM.gsh_list y TAB lo hi).

#[local] Notation MR := (APS.Mr A argH E ch model FULL).
#[local] Notation mHm := (mH FULL model A').

Lemma lit_start : forall a, 0 <= a < 2 ^ 64 -> estart E (SA (ELit 0) a) = a.
Proof. intros a Ha. unfold estart. cbn [a_base a_off edenot]. rewrite u64_lit by lia. lia. Qed.
Lemma lit_len : forall n, 0 <= n < 2 ^ 64 -> elenZ E (ELit n) = n.
Proof. intros n Hn. unfold elenZ. cbn [edenot]. apply u64_lit. lia. Qed.

Lemma piece_sound : forall K pos n, In K (kn ch) -> piece_len T TAB HULLS K pos = Some n ->
  img_hi A <= pos -> 0 <= pos -> pos + n <= 2 ^ 47 ->
  0 < n /\ forall x, pos <= x < pos + n -> MR (Z_to_bv 64 x) = Some (Z_to_bv 8 (GSM.gshw T TAB x)).
Proof.
  intros K pos n HK HP Hhull Hpos Hhi. pose proof (hk_kentry SEGS A LIMIT SINV argH ISP FS0 E ch R FULL model HC K HK) as KO.
  destruct K as [[kb a] w v | [kb a] len | [kb a] len k | | | | | | [kb a] len c |]; cbn [piece_len] in HP; try discriminate HP.
  - (* [comment removed for export] *)
    destruct kb as [kb0| | | | | | |]; try discriminate HP. destruct kb0; try discriminate HP.
    destruct w as [|[|w']]; try discriminate HP. destruct v as [c| | | | | | |]; try discriminate HP.
    destruct (Z.eqb_spec a pos) as [->|_]; [|discriminate HP].
    match type of HP with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate HP] end. injection HP as <-.
    apply andb_prop in Hb as [Hb Hok]. apply andb_prop in Hb as [C2 C3].
    apply Z.leb_le in C2. apply Z.ltb_lt in C3.
    split; [lia|]. intros x Hx. assert (x = pos) by lia. subst x.
    rewrite (const_ok_sound T TAB HSORT pos (pos + 1) c pos Hok ltac:(lia)).
    cbn [kentry_ok] in KO. destruct KO as (_ & Hfl & Hr).
    pose proof (flat_u E _ _ Hfl) as Hu. rewrite (lit_start pos ltac:(lia)) in Hu.
    cbn [rdn] in Hr.
    assert (Ead : adenot E (SA (ELit 0) pos) = Z_to_bv 64 pos) by (apply bv_eq; rewrite Hu, u64_lit by lia; reflexivity).
    rewrite Ead in Hr.
    assert (Hrom : seg_rom SEGS (Z_to_bv 64 pos) = None).
    { apply (APS.seg_rom_off_hull SEGS A SEGS_in_hull). rewrite u64_lit by lia. unfold APS.in_hull.
      apply andb_false_iff. right. apply Z.ltb_ge. exact Hhull. }
    destruct (MR (Z_to_bv 64 pos)) as [b|] eqn:Hb; [| rewrite Hrom in Hr; discriminate Hr].
    injection Hr as Hr. f_equal. rewrite Hr. cbn [edenot]. apply bv_eq. rewrite (u64_lit c) by lia. reflexivity.
  - (* [comment removed for export] *)
    destruct kb as [kb0| | | | | | |]; try discriminate HP. destruct kb0; try discriminate HP. destruct len as [l0| | | | | | |]; try discriminate HP.
    destruct (Z.eqb_spec a pos) as [->|_]; [|discriminate HP].
    match type of HP with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate HP] end. injection HP as <-.
    apply andb_prop in Hb as [C2 Hok]. apply Z.ltb_lt in C2.
    split; [exact C2|]. intros x Hx. rewrite (const_ok_sound T TAB HSORT pos (pos + l0) 0 x Hok Hx).
    cbn [kentry_ok] in KO. destruct KO as [_ KO]. rewrite (lit_start pos ltac:(lia)), (lit_len l0 ltac:(lia)) in KO.
    specialize (KO (x - pos) ltac:(lia)). replace (pos + (x - pos)) with x in KO by lia. exact KO.
  - (* [comment removed for export] *)
    destruct kb as [kb0| | | | | | |]; try discriminate HP. destruct kb0; try discriminate HP. destruct len as [l0| | | | | | |]; try discriminate HP.
    destruct (Z.eqb_spec a pos) as [->|_]; [|discriminate HP].
    match type of HP with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate HP] end. injection HP as <-.
    apply andb_prop in Hb as [Hb Hn]. apply andb_prop in Hb as [Hb Hap]. apply andb_prop in Hb as [C2 Hk].
    apply Z.ltb_lt in C2. apply Nat.leb_le in Hk.
    destruct (nth_error HULLS (k - K_GSH0)) as [[lo hi]|] eqn:Hnth; [|discriminate Hn].
    apply andb_prop in Hn as [N1 N2]. apply Z.eqb_eq in N1, N2. subst lo hi.
    split; [exact C2|]. intros x Hx. rewrite (apart_tab_gshw T TAB pos (pos + l0) x Hap Hx).
    cbn [kentry_ok] in KO. destruct KO as (_ & _ & KO). rewrite (lit_start pos ltac:(lia)), (lit_len l0 ltac:(lia)) in KO.
    specialize (KO (x - pos) ltac:(lia)). replace (pos + (x - pos)) with x in KO by lia. rewrite KO. f_equal.
    pose proof (HBL _ _ _ Hnth) as Eb. replace (K_GSH0 + (k - K_GSH0))%nat with k in Eb by lia. rewrite Eb.
    change (Z_to_bv 8 0) with ((fun z => Z_to_bv 8 z) 0). rewrite (map_nth (fun z => Z_to_bv 8 z)). cbv beta.
    rewrite (GSM.gsh_list_nth y TAB pos (pos + l0) (x - pos) ltac:(lia)). replace (pos + (x - pos)) with x by lia. reflexivity.
  - (* [comment removed for export] *)
    destruct kb as [kb0| | | | | | |]; try discriminate HP. destruct kb0; try discriminate HP. destruct len as [l0| | | | | | |]; try discriminate HP.
    destruct (Z.eqb_spec a pos) as [->|_]; [|discriminate HP].
    match type of HP with (if ?b then _ else _) = _ => destruct b eqn:Hb; [|discriminate HP] end. injection HP as <-.
    apply andb_prop in Hb as [Hb Hok]. apply andb_prop in Hb as [Hb C4]. apply andb_prop in Hb as [C2 C3].
    apply Z.ltb_lt in C2.
    split; [exact C2|]. intros x Hx. rewrite (const_ok_sound T TAB HSORT pos (pos + l0) c x Hok Hx).
    cbn [kentry_ok] in KO. destruct KO as [_ KO]. rewrite (lit_start pos ltac:(lia)), (lit_len l0 ltac:(lia)) in KO.
    specialize (KO (x - pos) ltac:(lia)). replace (pos + (x - pos)) with x in KO by lia. exact KO.
Qed.

Lemma find_piece_in : forall k pos n, find_piece T TAB HULLS k pos = Some n -> exists K, In K k /\ piece_len T TAB HULLS K pos = Some n.
Proof.
  induction k as [|K r IH]; intros pos n H; [discriminate H|]. cbn [find_piece] in H.
  destruct (piece_len T TAB HULLS K pos) as [m|] eqn:HP.
  - injection H as <-. exists K. split; [left; reflexivity | exact HP].
  - destruct (IH pos n H) as (K' & Hin & HP'). exists K'. split; [right; exact Hin | exact HP'].
Qed.

Lemma tile_sound : forall fuel pos hi, tile T TAB HULLS fuel (kn ch) pos hi = true -> img_hi A <= pos -> 0 <= pos -> pos <= hi -> hi <= 2 ^ 47 ->
  forall x, pos <= x < hi -> MR (Z_to_bv 64 x) = Some (Z_to_bv 8 (GSM.gshw T TAB x)).
Proof.
  induction fuel as [|f IH]; intros pos hi H Hh H0 Hle Hhi x Hx; cbn [tile] in H.
  - destruct (Z.eqb_spec pos hi); [lia | discriminate H].
  - destruct (Z.eqb_spec pos hi) as [|Nph]; [lia|].
    destruct (find_piece T TAB HULLS (kn ch) pos) as [n|] eqn:HF; [|discriminate H].
    apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
    destruct (find_piece_in _ _ _ HF) as (K & HK & HP).
    destruct (piece_sound K pos n HK HP Hh H0 ltac:(lia)) as [Hn Hc].
    destruct (Z.lt_ge_cases x (pos + n)) as [Hlt|Hge]; [exact (Hc x ltac:(lia))|].
    exact (IH (pos + n) hi H2 ltac:(lia) ltac:(lia) H1 Hhi x ltac:(lia)).
Qed.

(* [comment removed for export] *)
Theorem hs_gsh_sound : hs_gsh_ok T TAB HULLS A ch = true ->
  forall x, shad y (l_ilo y) <= x < shad y (l_ihi y) -> mHm (Z_to_bv 64 x) = Some (Z_to_bv 8 (GSM.gshw T TAB x)).
Proof.
  intros H x Hx. unfold hs_gsh_ok in H. cbv zeta in H.
  apply andb_prop in H as [H Ht]. apply andb_prop in H as [H C4]. apply andb_prop in H as [H C3]. apply andb_prop in H as [C1 C2].
  apply Z.leb_le in C1, C2, C3, C4.
  pose proof (tile_sound _ _ _ Ht C1 C2 C3 C4 x Hx) as HM.
  rewrite (hk_mr_some SEGS A LIMIT SINV argH ISP FS0 HULL_ok E ch R FULL model HC A' HA' (Z_to_bv 64 x)); [exact HM | rewrite HM; discriminate |].
  rewrite u64_lit by lia. lia.
Qed.

End Sound.
End HGSH.
