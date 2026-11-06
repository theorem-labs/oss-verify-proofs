(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import BrEnv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Fixpoint last_div' (m : Z) (ds : list (Z * nat)) : Z :=
  match ds with
  | [] => m
  | (d, _) :: rest => last_div' d rest
  end.

Lemma dsum_app : forall p s z m, dsum z m (p ++ s) = dsum z m p + dsum z (last_div' m p) s.
Proof.
  induction p as [|[d x] p IH]; intros s z m; cbn [app dsum last_div']; [lia|].
  rewrite IH. lia.
Qed.

Lemma chain_ok_app : forall p s t c m VT,
  chain_ok VT t c m (p ++ s) = true -> s <> [] -> chain_ok VT t c (last_div' m p) s = true.
Proof.
  induction p as [|[d x] p IH]; intros s t c m VT Hc Hs; cbn [app last_div'] in *; [exact Hc|].
  cbn [chain_ok] in Hc. apply andb_prop in Hc as [_ Hrest].
  destruct (p ++ s) as [|q r] eqn:Eps.
  - destruct p; [cbn in Eps; congruence | discriminate].
  - rewrite <- Eps in Hrest. exact (IH s t c d VT Hrest Hs).
Qed.

Lemma last_div_app p s : s <> [] -> last_div (p ++ s) = last_div s.
Proof.
  intros Hs. induction p as [|[d x] p IH]; [reflexivity|]. cbn [app].
  destruct (p ++ s) as [|q r] eqn:E.
  - destruct p; [cbn in E; congruence | discriminate].
  - cbn [last_div]. rewrite <- IH. reflexivity.
Qed.

Lemma chain_ok_prefix : forall p s t c m VT,
  chain_ok VT t c m (p ++ s) = true -> p <> [] -> chain_ok VT t c m p = true.
Proof.
  induction p as [|[d x] p IH]; intros s t c m VT Hc Hp; [congruence|].
  cbn [app chain_ok] in *. apply andb_prop in Hc as [Hh Hrest]. rewrite Hh. cbn [andb].
  destruct p as [|q p']; [reflexivity|].
  cbn [app] in Hrest. apply (IH s t c d VT); [exact Hrest | discriminate].
Qed.

Section Pure.
Variable segs : list Segment.
Variable rho : int -> word.
Variable xv : nat -> word.
Variable xb : nat -> list byte.
Variable VT : vtab.
Variable M : itrie region.
Variable TL : ttab.
Variable XT : list (int * AX2.lin).
Hypothesis Hrho0 : rho 0%uint63 = Z_to_bv 64 0.
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.
Hypothesis Hsep : regions_sep rho M.
Hypothesis HTL : tl_ok VT M TL = true.
Hypothesis HXT : xt_ok rho xv xb VT XT.

Local Notation E := (env_of rho xv xb VT).

(* [comment removed for export] *)
Variable tbnd : int -> option (Z * Z).
Hypothesis tbnd_sound : forall t lo hi, tbnd t = Some (lo, hi) -> lo <= bv_unsigned (rho t) <= hi.
Variable ts : int.
Variable tc : Z.
Variable AT : Z.
Hypothesis HAT : AT = bv_unsigned (rho ts) + tc - 8388608.
Variable in_entry : int -> Z -> Z -> bool.
Hypothesis in_entry_sound : forall t o n, in_entry t o n = true ->
  exists e, bv_unsigned (rho t) + o + n <= e /\ e <= AT /\ e mod 4096 = 0.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition krange_ok (e : AX2.expr) (lo hi : Z) : bool :=
  match e with
  | AX2.ELit z => (lo <=? z mod 2 ^ 64) && (z mod 2 ^ 64 <=? hi)
  | AX2.EVar x =>
      match vt_get VT x with
      | Some (VDiv t c d m) =>
          (0 <? d) &&
          match tbnd t with
          | Some (blo, bhi) =>
              (0 <=? blo + c) && (bhi + c <? 2 ^ 64)
              && (if m =? 0 then (lo <=? (blo + c) / d) && ((bhi + c) / d <=? hi)
                  else (0 <? m) && (lo <=? 0) && ((m - 1) / d <=? hi))
          | None => false
          end
      | Some (VVal (FV t w)) =>
          (t =? 0)%uint63 && (lo <=? wZ w) && (wZ w <=? hi)
      | _ => false
      end
  | _ =>
      match aview VT M TL XT (AX2.SA e 0) with
      | Some (t, o) =>
          match tbnd t with
          | Some (blo, bhi) => (0 <=? blo + o) && (bhi + o <? 2 ^ 64) && (lo <=? blo + o) && (bhi + o <=? hi)
          | None => false
          end
      | None => false
      end
  end.

Theorem krange_sound e lo hi :
  krange_ok e lo hi = true -> forall base, AX2S.kentry_ok segs E base (AX2.KRange e lo hi).
Proof.
  intros Hk base. cbn [AX2S.kentry_ok].
  assert (Hview : forall t o blo bhi,
            aview VT M TL XT (AX2.SA e 0) = Some (t, o) -> tbnd t = Some (blo, bhi) ->
            (0 <=? blo + o) && (bhi + o <? 2 ^ 64) && (lo <=? blo + o) && (bhi + o <=? hi) = true ->
            lo <= bv_unsigned (AX2.edenot E e) <= hi).
  { intros t o blo bhi Hav Hb Hc.
    apply andb_prop in Hc as [Hc H4]. apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply Z.leb_le in H1, H3, H4. apply Z.ltb_lt in H2.
    pose proof (aview_sound rho xv xb VT M TL XT HM Hrho0 HTL HXT _ t o Hav) as Hs.
    unfold AX2S.estart in Hs. cbn [AX2.a_base AX2.a_off] in Hs.
    pose proof (tbnd_sound t blo bhi Hb). lia. }
  assert (Hgen : forall e', e' = e ->
            match aview VT M TL XT (AX2.SA e' 0) with
            | Some (t, o) =>
                match tbnd t with
                | Some (blo, bhi) => (0 <=? blo + o) && (bhi + o <? 2 ^ 64) && (lo <=? blo + o) && (bhi + o <=? hi)
                | None => false
                end
            | None => false
            end = true -> lo <= bv_unsigned (AX2.edenot E e) <= hi).
  { intros e' -> Hc. destruct (aview VT M TL XT (AX2.SA e 0)) as [[t o]|]; [|discriminate].
    destruct (tbnd t) as [[blo bhi]|] eqn:Hb; [|discriminate]. exact (Hview t o blo bhi eq_refl Hb Hc). }
  destruct e as [z | x | op a b | op a b | op a b | op a b | sx l n a | sx k i n].
  3-8: exact (Hgen _ eq_refl Hk).
  - (* [comment removed for export] *)
    cbn [krange_ok] in Hk. apply andb_prop in Hk as [H1 H2]. apply Z.leb_le in H1, H2.
    cbn [AX2.edenot]. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). lia.
  - (* [comment removed for export] *)
    cbn [krange_ok] in Hk. cbn [AX2.edenot]. rewrite ev_env_of.
    destruct (vt_get VT x) as [[[t w]|t c d m|]|] eqn:Ex; try discriminate.
    + apply andb_prop in Hk as [Hk H2]. apply andb_prop in Hk as [H0 H1].
      apply Uint63.eqb_spec in H0. subst t. apply Z.leb_le in H1, H2.
      cbn [vden]. rewrite (fk_dv_conc rho w Hrho0), wbv_unsigned. lia.
    + apply andb_prop in Hk as [Hd Hk]. apply Z.ltb_lt in Hd.
      destruct (tbnd t) as [[blo bhi]|] eqn:Hb; [|discriminate].
      apply andb_prop in Hk as [Hk Hr]. apply andb_prop in Hk as [H1 H2].
      apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      pose proof (tbnd_sound t blo bhi Hb) as Hbt.
      set (z := bv_unsigned (rho t) + c) in *.
      assert (Hz : 0 <= z < 2 ^ 64) by (unfold z; lia).
      cbn [vden]. fold z.
      destruct (m =? 0) eqn:Em.
      * apply andb_prop in Hr as [H3 H4]. apply Z.leb_le in H3, H4.
        assert (Hdg : (blo + c) / d <= digit z d m <= (bhi + c) / d).
        { unfold digit. rewrite Em. split; apply Z.div_le_mono; unfold z; lia. }
        assert (0 <= digit z d m <= z).
        { apply digit_range; [lia | exact Hd |]. apply Z.eqb_eq in Em. lia. }
        rewrite br_lit_small by lia. lia.
      * apply andb_prop in Hr as [Hr H4]. apply andb_prop in Hr as [Hm H3].
        apply Z.ltb_lt in Hm. apply Z.leb_le in H3, H4.
        assert (Hdg : 0 <= digit z d m <= (m - 1) / d).
        { unfold digit. rewrite Em. pose proof (Z.mod_pos_bound z m Hm).
          split; [apply Z.div_pos; lia | apply Z.div_le_mono; lia]. }
        assert (0 <= digit z d m <= z) by (apply digit_range; lia).
        rewrite br_lit_small by lia. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kalign_ok (e : AX2.expr) (m : Z) : bool :=
  (0 <? m) &&
  match aview VT M TL XT (AX2.SA e 0) with
  | Some (t, o) =>
      (o mod m =? 0)
      && (((t =? 0)%uint63)
          || match iget t M with
             | Some rg => (to_Z (rg_align rg) <=? 62) && ((2 ^ to_Z (rg_align rg)) mod m =? 0)
             | None => false
             end)
  | None => false
  end.

Theorem kalign_sound e m :
  kalign_ok e m = true -> forall base, AX2S.kentry_ok segs E base (AX2.KAlign e m).
Proof.
  unfold kalign_ok. intros Hk base. apply andb_prop in Hk as [Hm Hk]. apply Z.ltb_lt in Hm.
  destruct (aview VT M TL XT (AX2.SA e 0)) as [[t o]|] eqn:Hav; [|discriminate].
  apply andb_prop in Hk as [Ho Hal]. apply Z.eqb_eq in Ho.
  cbn [AX2S.kentry_ok]. split; [exact Hm|].
  pose proof (aview_sound rho xv xb VT M TL XT HM Hrho0 HTL HXT _ t o Hav) as Hs.
  unfold AX2S.estart in Hs. cbn [AX2.a_base AX2.a_off] in Hs. rewrite Z.add_0_r in Hs. rewrite Hs.
  assert (Hr : bv_unsigned (rho t) mod m = 0).
  { apply orb_prop in Hal as [Ht|Hal].
    - apply Uint63.eqb_spec in Ht. subst t. rewrite Hrho0. reflexivity.
    - destruct (iget t M) as [rg|] eqn:Hg; [|discriminate].
      apply andb_prop in Hal as [_ Hpd]. apply Z.eqb_eq in Hpd.
      destruct (HM t rg Hg) as (_ & _ & _ & _ & Hmod & _).
      apply Z.mod_divide in Hpd; [|lia].
      pose proof (i63_range (rg_align rg)).
      assert (0 < 2 ^ to_Z (rg_align rg)) by (apply Z.pow_pos_nonneg; lia).
      apply Z.mod_divide in Hmod; [|lia]. apply Z.mod_divide; [lia|].
      exact (Z.divide_trans _ _ _ Hpd Hmod). }
  rewrite Z.add_mod by lia. rewrite Hr, Ho. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition inreg (t : int) (o n : Z) : bool :=
  match iget t M with
  | Some rg => (to_Z (rg_lo rg) <=? o) && (o + n <=? to_Z (rg_len rg))
  | None => false
  end.

Definition above_top (t : int) (o : Z) : bool := (t =? ts)%uint63 && (tc - 8388608 <=? o).

(* [comment removed for export] *)
Fixpoint pg_split (ds : list (Z * nat)) : list (Z * nat) * list (Z * nat) :=
  match ds with
  | [] => ([], [])
  | (d, x) :: rest => if 4096 <=? d then let (p, s) := pg_split rest in ((d, x) :: p, s) else ([], ds)
  end.

Lemma pg_split_app ds : fst (pg_split ds) ++ snd (pg_split ds) = ds.
Proof.
  induction ds as [|[d x] rest IH]; [reflexivity|]. cbn [pg_split].
  destruct (4096 <=? d); [|reflexivity]. destruct (pg_split rest) as [p s]. cbn [fst snd app] in *.
  rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)
Definition pgview (a : AX2.saddr) : option Z :=
  match tl_get TL ts with
  | Some td =>
      let l := elin VT (AX2.a_base a) in
      let p := fst (pg_split (td_digits td)) in
      let k0 := AX2.snorm (fst l) in
      if (td_c td =? tc) && (last_div' 0 p =? 4096) && terms_eqb (snd l) (tag_terms p)
         && (0 <=? k0) && (k0 <? 2 ^ 62)
         && match iget ts M with Some _ => true | None => false end
      then Some (k0 + AX2.a_off a) else None
  | None => None
  end.

Lemma pgview_sound a k :
  pgview a = Some k ->
  AX2S.estart E a = (bv_unsigned (rho ts) + tc) / 4096 * 4096 + k.
Proof.
  unfold pgview. intros Hp. destruct (tl_get TL ts) as [td|] eqn:Hg; [|discriminate].
  set (l := elin VT (AX2.a_base a)) in *.
  set (p := fst (pg_split (td_digits td))) in *.
  set (s := snd (pg_split (td_digits td))).
  set (k0 := AX2.snorm (fst l)) in *.
  match type of Hp with (if ?c then _ else _) = _ => destruct c eqn:Ec end; [|discriminate].
  injection Hp as <-.
  apply andb_prop in Ec as [Ec Hreg]. destruct (iget ts M) as [rgs|] eqn:Hgs; [|discriminate].
  apply andb_prop in Ec as [Ec Hk1]. apply andb_prop in Ec as [Ec Hk0].
  apply andb_prop in Ec as [Ec Hte]. apply andb_prop in Ec as [Hc Hld].
  apply Z.eqb_eq in Hc, Hld. apply Z.leb_le in Hk0. apply Z.ltb_lt in Hk1. apply terms_eqb_eq in Hte.
  pose proof (tl_In_ok VT M TL HTL ts td (tl_get_In TL ts td Hg)) as Htd.
  destruct (td_ok_z rho VT M HM ts td Htd) as [Hz Hal]. rewrite Hc in Hz, Hal.
  set (z := bv_unsigned (rho ts) + tc) in *.
  pose proof Htd as Htd'. unfold td_ok in Htd'. apply andb_prop in Htd' as [Htd' _].
  apply andb_prop in Htd' as [Htd' Hch]. rewrite Hc in Hch.
  pose proof (pg_split_app (td_digits td)) as Happ. fold p s in Happ.
  assert (Hpne : p <> []).
  { intros Ep. rewrite Ep in Hld. cbn in Hld. lia. }
  (* [comment removed for export] *)
  assert (Hsum : dsum z 0 p = z / 4096 * 4096).
  { pose proof (dsum_chain rho xv xb VT (td_digits td) z 0 ltac:(lia) ltac:(lia) ts tc Hch Hal) as Hall.
    cbn [Z.eqb] in Hall. rewrite <- Happ in Hall. rewrite dsum_app, Hld in Hall.
    destruct s as [|q s'] eqn:Es.
    - cbn [dsum] in Hall. rewrite <- Happ, app_nil_r in Hal.
      assert (Hl4 : last_div p = 4096).
      { clear - Hld Hpne. revert Hld. generalize 0. induction p as [|[d x] p IH]; intros m Hld; [congruence|].
        cbn [last_div' last_div] in *. destruct p as [|q p']; [exact Hld|]. apply (IH ltac:(discriminate) d Hld). }
      rewrite Hl4 in Hal. Z.div_mod_to_equations. lia.
    - assert (Hcs : chain_ok VT ts tc 4096 (q :: s') = true).
      { rewrite <- Hld. apply chain_ok_app; [rewrite Happ; exact Hch | discriminate]. }
      assert (Hals : z mod last_div (q :: s') = 0).
      { rewrite <- (last_div_app p (q :: s')) by discriminate. rewrite Happ. exact Hal. }
      rewrite (dsum_chain rho xv xb VT (q :: s') z 4096 ltac:(lia) ltac:(lia) ts tc Hcs Hals) in Hall.
      change (4096 =? 0) with false in Hall. cbv iota in Hall. Z.div_mod_to_equations. lia. }
  pose proof (chain_tden rho xv xb VT p ts tc 0 z
                (chain_ok_prefix p s ts tc 0 VT ltac:(rewrite Happ; exact Hch) Hpne)
                eq_refl Hz ltac:(lia)) as Ht.
  rewrite Hsum in Ht.
  pose proof (elin_sound rho xv xb VT Hrho0 (AX2.a_base a)) as Hl. fold l in Hl.
  unfold AX2S.lden, AX2S.uE in Hl. rewrite Hte in Hl.
  pose proof (br_u64 (AX2.edenot E (AX2.a_base a))) as Hu.
  assert (Ee : bv_unsigned (AX2.edenot E (AX2.a_base a)) = z / 4096 * 4096 + k0).
  { apply br_eqm_small; [|exact Hu|].
    - apply AX2S.eqm_sym. eapply AX2S.eqm_trans; [|exact Hl].
      destruct Ht as [q1 Hq1]. destruct (AX2S.eqm_snorm (fst l)) as [q2 Hq2]. fold k0 in Hq2.
      exists (q2 - q1). lia.
    - assert (0 <= z / 4096 * 4096 <= z) by (Z.div_mod_to_equations; lia).
      destruct (HM ts rgs Hgs) as (_ & _ & Hb63 & _). pose proof (i63_range (rg_len rgs)).
      apply andb_prop in Htd' as [Htd' _]. apply andb_prop in Htd' as [_ Hc62]. apply Z.ltb_lt in Hc62.
      rewrite Hc in Hc62. unfold z. lia. }
  unfold AX2S.estart. rewrite Ee. lia.
Qed.

(* [comment removed for export] *)
Definition kdisj_dir (a1 : AX2.saddr) (n1 : Z) (a2 : AX2.saddr) (n2 : Z) : bool :=
  match aview VT M TL XT a2 with
  | Some (t2, o2) =>
      match aview VT M TL XT a1 with
      | Some (t1, o1) =>
          if (t1 =? t2)%uint63 then (o1 + n1 <=? o2) || (o2 + n2 <=? o1)
          else (inreg t1 o1 n1 && inreg t2 o2 n2)
               || (above_top t1 o1 && in_entry t2 o2 n2)
      | None =>
          match pgview a1 with
          | Some k1 => (-8388608 <=? k1) && in_entry t2 o2 n2
          | None => false
          end
      end
  | None => false
  end.

Definition kdisj_ok (a1 : AX2.saddr) (n1 : AX2.expr) (a2 : AX2.saddr) (n2 : AX2.expr) : bool :=
  match n1, n2 with
  | AX2.ELit l1, AX2.ELit l2 =>
      (0 <=? l1) && (l1 <? 2 ^ 62) && (0 <=? l2) && (l2 <? 2 ^ 62)
      && (kdisj_dir a1 l1 a2 l2 || kdisj_dir a2 l2 a1 l1)
  | _, _ => false
  end.

Lemma kdisj_dir_sound a1 n1 a2 n2 :
  0 <= n1 -> 0 <= n2 -> kdisj_dir a1 n1 a2 n2 = true ->
  AX2S.estart E a1 + n1 <= AX2S.estart E a2 \/ AX2S.estart E a2 + n2 <= AX2S.estart E a1.
Proof.
  intros Hn1 Hn2. unfold kdisj_dir. intros Hk.
  destruct (aview VT M TL XT a2) as [[t2 o2]|] eqn:Hv2; [|discriminate].
  pose proof (aview_sound rho xv xb VT M TL XT HM Hrho0 HTL HXT _ t2 o2 Hv2) as Hs2.
  destruct (aview VT M TL XT a1) as [[t1 o1]|] eqn:Hv1.
  - pose proof (aview_sound rho xv xb VT M TL XT HM Hrho0 HTL HXT _ t1 o1 Hv1) as Hs1.
    destruct (t1 =? t2)%uint63 eqn:Et.
    + apply Uint63.eqb_spec in Et. subst t2. apply orb_prop in Hk as [Hk|Hk]; apply Z.leb_le in Hk; lia.
    + assert (Hne : t1 <> t2) by (intros ->; rewrite Uint63.eqb_refl in Et; discriminate).
      apply orb_prop in Hk as [Hk|Hk].
      * apply andb_prop in Hk as [Hr1 Hr2]. unfold inreg in Hr1, Hr2.
        destruct (iget t1 M) as [rg1|] eqn:Hg1; [|discriminate].
        destruct (iget t2 M) as [rg2|] eqn:Hg2; [|discriminate].
        apply andb_prop in Hr1 as [A1 A2]. apply andb_prop in Hr2 as [B1 B2].
        apply Z.leb_le in A1, A2, B1, B2.
        destruct (Hsep t1 t2 rg1 rg2 Hne Hg1 Hg2) as [Hd|Hd]; lia.
      * apply andb_prop in Hk as [Ha He]. unfold above_top in Ha. apply andb_prop in Ha as [Ha1 Ha2].
        apply Uint63.eqb_spec in Ha1. subst t1. apply Z.leb_le in Ha2.
        destruct (in_entry_sound t2 o2 n2 He) as (e & He1 & He2 & _). right. lia.
  - destruct (pgview a1) as [k1|] eqn:Hp; [|discriminate].
    apply andb_prop in Hk as [Hk1 He]. apply Z.leb_le in Hk1.
    pose proof (pgview_sound a1 k1 Hp) as Hs1.
    destruct (in_entry_sound t2 o2 n2 He) as (e & He1 & He2 & He3). right.
    rewrite Hs1, Hs2. rewrite HAT in He2.
    set (z := bv_unsigned (rho ts) + tc) in *.
    assert (Hq : e = 4096 * (e / 4096)) by (pose proof (Z.div_mod e 4096 ltac:(lia)); lia).
    set (q := e / 4096) in *.
    assert (Hle : q + 2048 <= z / 4096) by (apply Z.div_le_lower_bound; lia).
    lia.
Qed.

Theorem kdisj_sound a1 n1 a2 n2 :
  kdisj_ok a1 n1 a2 n2 = true -> forall base, AX2S.kentry_ok segs E base (AX2.KDisj a1 n1 a2 n2).
Proof.
  unfold kdisj_ok. intros Hk base.
  destruct n1 as [l1| | | | | | |]; try discriminate. destruct n2 as [l2| | | | | | |]; try discriminate.
  apply andb_prop in Hk as [Hk Hd]. apply andb_prop in Hk as [Hk H4]. apply andb_prop in Hk as [Hk H3].
  apply andb_prop in Hk as [H1 H2]. apply Z.leb_le in H1, H3. apply Z.ltb_lt in H2, H4.
  cbn [AX2S.kentry_ok]. unfold AX2S.elenZ. cbn [AX2.edenot].
  rewrite !br_lit_small by lia.
  apply orb_prop in Hd as [Hd|Hd].
  - exact (kdisj_dir_sound a1 l1 a2 l2 H1 H3 Hd).
  - destruct (kdisj_dir_sound a2 l2 a1 l1 H3 H1 Hd) as [Hx|Hx]; [right | left]; exact Hx.
Qed.

End Pure.
