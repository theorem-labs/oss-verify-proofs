(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRn FxHandoff FxHoBuild.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Common.Br Require Import BrEnv BrMem.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ttab_e : Type := list (int * AX2.expr).

Fixpoint tt_get (TT : ttab_e) (t : int) : option AX2.expr :=
  match TT with
  | [] => None
  | (t', e) :: r => if (t' =? t)%uint63 then Some e else tt_get r t
  end.

Definition rho_of (TT : ttab_e) (E : AX2.env) : int -> word :=
  fun t => if (t =? 0)%uint63 then Z_to_bv 64 0
           else match tt_get TT t with Some e => AX2.edenot E e | None => Z_to_bv 64 0 end.

Lemma rho_of_0 TT E : rho_of TT E 0%uint63 = Z_to_bv 64 0.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Fixpoint tt_wf (TT : ttab_e) : bool :=
  match TT with
  | [] => true
  | (t, _) :: r => negb (t =? 0)%uint63 && negb (existsb (fun p => (fst p =? t)%uint63) r) && tt_wf r
  end.

Lemma tt_get_In : forall TT t e, tt_wf TT = true -> In (t, e) TT -> tt_get TT t = Some e /\ t <> 0%uint63.
Proof.
  induction TT as [|[t' e'] r IH]; intros t e Hwf Hin; [destruct Hin|].
  cbn [tt_wf] in Hwf. apply andb_prop in Hwf as [Hwf Hr]. apply andb_prop in Hwf as [H0 Hnd].
  cbn [tt_get]. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. rewrite Uint63.eqb_refl. split; [reflexivity|].
    intros ->. rewrite Uint63.eqb_refl in H0. discriminate.
  - destruct (t' =? t)%uint63 eqn:Et; [|exact (IH t e Hr Hin)].
    apply Uint63.eqb_spec in Et. subst t'. exfalso.
    apply negb_true_iff in Hnd. assert (Hex : existsb (fun p => (fst p =? t)%uint63) r = true).
    { apply existsb_exists. exists (t, e). split; [exact Hin|]. cbn [fst]. apply Uint63.eqb_refl. }
    rewrite Hex in Hnd. discriminate.
Qed.

Lemma env_eta rho E : env_of rho (AX2.ev E) (AX2.eb E) [] = E.
Proof. destruct E as [f g]. reflexivity. Qed.

Definition xt_of (TT : ttab_e) : list (int * AX2.lin) := map (fun p => (fst p, AX2.lin_of (snd p))) TT.

Lemma xt_of_ok TT E : tt_wf TT = true ->
  xt_ok (rho_of TT E) (AX2.ev E) (AX2.eb E) [] (xt_of TT).
Proof.
  intros Hwf. unfold xt_ok, xt_of. rewrite env_eta. apply Forall_forall. intros p Hp.
  apply in_map_iff in Hp as ([t e] & <- & Hin). cbn [fst snd].
  destruct (tt_get_In TT t e Hwf Hin) as [Hg Hne].
  unfold rho_of. destruct (t =? 0)%uint63 eqn:Et; [apply Uint63.eqb_spec in Et; contradiction|].
  rewrite Hg. apply AX2S.lin_of_sound.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Full.
Variable segs : list Segment.
Variable H : word -> bool.
Variable FULL : word -> option byte.
(* [comment removed for export] *)
Hypothesis Hnoseg : forall x, H x = true -> PropExec.seg_rom segs x = None.

Lemma rview_seg_rom m x : rview segs m x = match m x with Some b => Some b | None => PropExec.seg_rom segs x end.
Proof. reflexivity. Qed.

Lemma rdn_bytes : forall n m a bs, rdn segs m a n = Some bs ->
  forall j, (j < n)%nat -> rview segs m (aoff a j) = nth_error bs j.
Proof.
  induction n as [|n IH]; intros m a bs Hr j Hj; [lia|]. cbn [rdn] in Hr.
  destruct (match m a with Some b => Some b | None => PropExec.seg_rom segs a end) as [b|] eqn:Hb; [|discriminate].
  destruct (rdn segs m (a + 1)%bv n) as [rest|] eqn:Hrest; [|discriminate]. injection Hr as <-.
  destruct j as [|j].
  - rewrite aoff_0, rview_seg_rom. exact Hb.
  - rewrite <- aoff_S. cbn [nth_error]. apply (IH m _ _ Hrest). lia.
Qed.

Lemma rview_full x b : rview segs (mrestrict H FULL) x = Some b -> rview segs FULL x = Some b.
Proof.
  rewrite !rview_seg_rom. unfold mrestrict. destruct (H x) eqn:Hx; [|tauto].
  rewrite (Hnoseg x Hx). discriminate.
Qed.

Theorem rdn_full n a bs : rdn segs (mrestrict H FULL) a n = Some bs ->
  forall j, (j < n)%nat -> rview segs FULL (aoff a j) = nth_error bs j.
Proof.
  intros Hr j Hj. pose proof (rdn_bytes n _ a bs Hr j Hj) as Hb.
  destruct (nth_error bs j) as [b|] eqn:Hn.
  - apply rview_full. exact Hb.
  - exfalso. apply nth_error_None in Hn. pose proof (rdn_length segs _ n a bs Hr). lia.
Qed.

Lemma wview_full x : wview segs (mrestrict H FULL) x <> None -> wview segs FULL x <> None.
Proof.
  unfold wview, mrestrict. destruct (H x) eqn:Hx.
  - destruct (FULL x); [discriminate | tauto].
  - tauto.
Qed.
End Full.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Facts.
Variable segs : list Segment.
Variable E : AX2.env.
Variable TT : ttab_e.
Variable M : itrie region.          (* [comment removed for export] *)
Variable H : word -> bool.
Variable ms : machine_state.
Hypothesis HTT : tt_wf TT = true.
Hypothesis Hnoseg : forall x, H x = true -> PropExec.seg_rom segs x = None.
(* [comment removed for export] *)
Variable img_lo img_hi : Z.
Hypothesis Hhull : forall a, img_lo <= a < img_hi -> H (Z_to_bv 64 a) = false.

Local Notation rho := (rho_of TT E).
Local Notation XT := (xt_of TT).
Hypothesis HM : forall t rg, iget t M = Some rg -> region_ok rho t rg.

Lemma rv_tl : tl_ok [] M [] = true. Proof. reflexivity. Qed.
Lemma rv_teq : teq_ok rho []. Proof. constructor. Qed.

(* [comment removed for export] *)
Definition vview (v : AX2.expr) : option fval :=
  let l := elin [] v in
  match snd l with
  | [] => Some (FV 0 (w_of_Z (fst l)))
  | ts => match find_tag [] XT ts with
          | Some (t, lt) => Some (FV t (w_of_Z (fst l - fst lt)))
          | None => None
          end
  end.

Definition vview_ok (v : AX2.expr) : option fval :=
  match vview v with
  | Some fv => if val_match [] [] XT [] v fv then Some fv else None
  | None => None
  end.

Lemma vview_ok_sound v fv : vview_ok v = Some fv -> AX2.edenot E v = dv rho fv.
Proof.
  unfold vview_ok. destruct (vview v) as [fv'|]; [|discriminate].
  destruct (val_match [] [] XT [] v fv') eqn:Hvm; [|discriminate]. intros Hq. injection Hq as <-.
  pose proof (val_match_sound rho (AX2.ev E) (AX2.eb E) [] M [] XT [] HM (rho_of_0 TT E) rv_tl (xt_of_ok TT E HTT) rv_teq
                v fv' Hvm) as Hs.
  rewrite env_eta in Hs. exact Hs.
Qed.

Definition oint (z : Z) : option int := if (0 <=? z) && (z <? 2 ^ 62) then Some (of_Z z) else None.

Lemma oint_spec z i : oint z = Some i -> to_Z i = z /\ 0 <= z < 2 ^ 62.
Proof.
  unfold oint. destruct ((0 <=? z) && (z <? 2 ^ 62)) eqn:Hc; [|discriminate]. intros Hq. injection Hq as <-.
  apply andb_prop in Hc as [H0 H1]. apply Z.leb_le in H0. apply Z.ltb_lt in H1.
  split; [apply of_Z_small; lia | lia].
Qed.

(* [comment removed for export] *)
Definition in_rg (t : int) (o n : Z) : bool :=
  match iget t M with
  | Some rg => (to_Z (rg_lo rg) <=? o) && (o + n <=? to_Z (rg_len rg))
  | None => false
  end.

Definition fact_of_kentry (K : AX2.kentry) : option hfact :=
  match K with
  | AX2.KWord a w v =>
      match aview [] M [] XT a, vview_ok v with
      | Some (t, o), Some fv =>
          if negb (in_rg t o (Z.of_nat w)) then None else
          match oint o with
          | Some oi => if Nat.eqb w 8 then Some (HVal t oi fv)
                       else if (Nat.leb 1 w && Nat.leb w 8)%bool then
                              (* [comment removed for export] *)
                              Some (if (vtag fv =? 0)%uint63 then HCell t oi (of_Z (Z.of_nat w)) (vw fv)
                                    else HBytes t oi (of_Z (Z.of_nat w)) fv)
                            else None
          | None => None
          end
      | _, _ => None
      end
  | AX2.KWr a (AX2.ELit n) | AX2.KUnk a (AX2.ELit n) =>
      match aview [] M [] XT a with
      | Some (t, o) => if negb (in_rg t o n) then None else
                       match oint o, oint n with Some oi, Some ni => Some (HWr t oi ni) | _, _ => None end
      | None => None
      end
  | AX2.KZero a (AX2.ELit n) =>
      match aview [] M [] XT a with
      | Some (t, o) => if negb (in_rg t o n) then None else
                       match oint o, oint n with Some oi, Some ni => Some (HZero t oi ni) | _, _ => None end
      | None => None
      end
  | AX2.KImg lo hi =>
      if (img_lo <=? lo) && (hi <=? img_hi) then
        match oint lo, oint hi with Some li, Some hi' => Some (HClear li hi') | _, _ => None end
      else None
  | _ => None
  end.

Lemma aview_adr a t o n :
  aview [] M [] XT a = Some (t, o) -> AX2S.flat E a n -> 0 <= o ->
  AX2.adenot E a = adr rho t o /\ AX2S.estart E a = bv_unsigned (rho t) + o.
Proof.
  intros Hav Hflat Ho.
  pose proof (aview_sound rho (AX2.ev E) (AX2.eb E) [] M [] XT HM (rho_of_0 TT E) rv_tl (xt_of_ok TT E HTT) a t o Hav) as Hs.
  rewrite env_eta in Hs. split; [|exact Hs].
  apply bv_eq. rewrite (AX2S.flat_u _ _ _ Hflat), Hs.
  destruct Hflat as (F1 & F2 & F3 & F4). rewrite Hs in F2.
  symmetry. apply (adr_unsigned rho t o Ho). exact F2.
Qed.

Theorem fact_of_sound K f :
  fact_of_kentry K = Some f ->
  AX2S.kentry_ok segs E (mrestrict H (ms_mem ms)) K ->
  hholds segs rho ms f.
Proof.
  intros Hf HK. destruct K as [a w v | a n | a n j | lo hi' | e m0 | e lo hi' | a n | a1 n1 a2 n2 | a n c | a n];
    cbn [fact_of_kentry] in Hf; try discriminate.
  - (* [comment removed for export] *)
    destruct (aview [] M [] XT a) as [[t o]|] eqn:Hav; [|discriminate].
    destruct (vview_ok v) as [fv|] eqn:Hv; [|discriminate].
    destruct (negb (in_rg t o (Z.of_nat w))); [discriminate|].
    destruct (oint o) as [oi|] eqn:Ho; [|discriminate].
    destruct (oint_spec o oi Ho) as [Eoi Hor].
    destruct HK as (Hw & Hflat & Hr).
    destruct (aview_adr a t o _ Hav Hflat ltac:(lia)) as [Ead _].
    pose proof (vview_ok_sound v fv Hv) as Ev.
    assert (Hbytes : forall j, (j < w)%nat ->
              rview segs (ms_mem ms) (adr rho t (to_Z oi + Z.of_nat j)) = nth_error (wbytes8 (dv rho fv)) j).
    { intros j Hj. pose proof (rdn_full segs H (ms_mem ms) Hnoseg w _ _ Hr j Hj) as Hb.
      rewrite Ead, aoff_adr in Hb. rewrite Eoi, Hb. unfold word_to_le_bytes, wbytes8. rewrite Ev.
      rewrite !Z_to_le_bytes_nth by lia. reflexivity. }
    destruct (Nat.eqb w 8) eqn:E8.
    + apply Nat.eqb_eq in E8. subst w. injection Hf as <-. cbn [hholds]. exact Hbytes.
    + destruct (Nat.leb 1 w && Nat.leb w 8)%bool eqn:Ew; [|discriminate]. injection Hf as <-.
      destruct (vtag fv =? 0)%uint63 eqn:Etag.
      * cbn [hholds]. intros j Hj. rewrite Hbytes by (rewrite of_Z_small in Hj by lia; lia).
        rewrite (FxMemSound.dv_tag0' rho (rho_of_0 TT E) fv Etag), FxMemSound.wbytes8_wbv. reflexivity.
      * cbn [hholds]. intros j Hj. apply Hbytes.
        rewrite of_Z_small in Hj by lia. lia.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate.
    destruct (aview [] M [] XT a) as [[t o]|] eqn:Hav; [|discriminate].
    destruct (negb (in_rg t o n)); [discriminate|].
    destruct (oint o) as [oi|] eqn:Ho; [|discriminate]. destruct (oint n) as [ni|] eqn:Hn; [|discriminate].
    injection Hf as <-. destruct (oint_spec o oi Ho) as [Eoi Hor]. destruct (oint_spec n ni Hn) as [Eni Hnr].
    destruct HK as (Hflat & Hz). unfold AX2S.elenZ in *. cbn [AX2.edenot] in *.
    rewrite br_lit_small in * by lia.
    destruct (aview_adr a t o _ Hav Hflat ltac:(lia)) as [_ Est].
    cbn [hholds]. intros j Hj. rewrite Eoi. rewrite Eni in Hj.
    specialize (Hz j Hj). rewrite Est in Hz.
    assert (Ea : Z_to_bv 64 (bv_unsigned (rho t) + o + j) = adr rho t (o + j)).
    { unfold adr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. f_equal. lia. }
    rewrite Ea in Hz. apply (rview_full segs H (ms_mem ms) Hnoseg).
    rewrite rview_seg_rom. rewrite Hz. reflexivity.
  - (* [comment removed for export] *)
    destruct ((img_lo <=? lo) && (hi' <=? img_hi)) eqn:Hc; [|discriminate].
    apply andb_prop in Hc as [Hc1 Hc2]. apply Z.leb_le in Hc1, Hc2.
    destruct (oint lo) as [li|] eqn:Hlo; [|discriminate]. destruct (oint hi') as [hi2|] eqn:Hhi; [|discriminate].
    injection Hf as <-. destruct (oint_spec _ _ Hlo) as [El _]. destruct (oint_spec _ _ Hhi) as [Eh _].
    destruct HK as (_ & _ & Hn). cbn [hholds]. intros a Ha. rewrite El, Eh in Ha.
    specialize (Hn a Ha). unfold mrestrict in Hn. rewrite (Hhull a ltac:(lia)) in Hn. exact Hn.
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate.
    destruct (aview [] M [] XT a) as [[t o]|] eqn:Hav; [|discriminate].
    destruct (negb (in_rg t o n)); [discriminate|].
    destruct (oint o) as [oi|] eqn:Ho; [|discriminate]. destruct (oint n) as [ni|] eqn:Hn; [|discriminate].
    injection Hf as <-. destruct (oint_spec o oi Ho) as [Eoi Hor]. destruct (oint_spec n ni Hn) as [Eni Hnr].
    destruct HK as (Hflat & Hs). unfold AX2S.elenZ in *. cbn [AX2.edenot] in *.
    rewrite br_lit_small in * by lia.
    destruct (aview_adr a t o _ Hav Hflat ltac:(lia)) as [_ Est].
    cbn [hholds]. intros j Hj. rewrite Eoi. rewrite Eni in Hj.
    specialize (Hs j 1%nat ltac:(lia) ltac:(lia)). rewrite Est in Hs.
    assert (Ea : Z_to_bv 64 (bv_unsigned (rho t) + o + j) = adr rho t (o + j)).
    { unfold adr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. f_equal. lia. }
    rewrite Ea in Hs. cbn [store_ok] in Hs. apply (wview_full segs H (ms_mem ms)).
    destruct (wview segs (mrestrict H (ms_mem ms)) (adr rho t (o + j))); [discriminate | discriminate Hs].
  - (* [comment removed for export] *)
    destruct n as [n| | | | | | |]; try discriminate.
    destruct (aview [] M [] XT a) as [[t o]|] eqn:Hav; [|discriminate].
    destruct (negb (in_rg t o n)); [discriminate|].
    destruct (oint o) as [oi|] eqn:Ho; [|discriminate]. destruct (oint n) as [ni|] eqn:Hn; [|discriminate].
    injection Hf as <-. destruct (oint_spec o oi Ho) as [Eoi Hor]. destruct (oint_spec n ni Hn) as [Eni Hnr].
    destruct HK as (Hflat & Hd). unfold AX2S.elenZ in *. cbn [AX2.edenot] in *.
    rewrite br_lit_small in * by lia.
    destruct (aview_adr a t o _ Hav Hflat ltac:(lia)) as [_ Est].
    cbn [hholds]. intros j Hj. rewrite Eoi. rewrite Eni in Hj.
    specialize (Hd j Hj). rewrite Est in Hd.
    assert (Ea : Z_to_bv 64 (bv_unsigned (rho t) + o + j) = adr rho t (o + j)).
    { unfold adr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
      change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. f_equal. lia. }
    rewrite Ea in Hd. unfold wview. unfold mrestrict in Hd.
    destruct (H (adr rho t (o + j))); [congruence|]. destruct (ms_mem ms (adr rho t (o + j))); [discriminate | congruence].
Qed.


(* [comment removed for export] *)
Definition fillw (c : Z) : w64 := let b := of_Z c in w_of_bytes8 b b b b b b b b.

Definition fill_cov1 (K : AX2.kentry) : list (int * Z * Z * Z) :=
  match K with
  | AX2.KFill a (AX2.ELit n) c =>
      match aview [] M [] XT a with
      | Some (t, o) => if in_rg t o n && (0 <=? o) && (0 <=? n) && (o + n <? 2 ^ 62) && (0 <=? c) && (c <? 256) then [(t, o, n, c)] else []
      | None => []
      end
  | _ => []
  end.

Definition fill_ok (q : int * Z * Z * Z) : Prop :=
  let '(t, o, n, c) := q in
  0 <= o /\ o + n < 2 ^ 62 /\ 0 <= c < 256
  /\ forall i, 0 <= i < n -> rview segs (ms_mem ms) (adr rho t (o + i)) = Some (Z_to_bv 8 c).

Lemma fill_cov1_sound K q :
  In q (fill_cov1 K) -> AX2S.kentry_ok segs E (mrestrict H (ms_mem ms)) K -> fill_ok q.
Proof.
  intros Hin HK. destruct K as [a w v | a n | a n j | lo hi' | e m0 | e lo hi' | a n | a1 n1 a2 n2 | a n c | a n];
    cbn [fill_cov1] in Hin; try (destruct Hin; fail).
  destruct n as [n| | | | | | |]; try (destruct Hin; fail).
  destruct (aview [] M [] XT a) as [[t o]|] eqn:Hav; [|destruct Hin].
  destruct (in_rg t o n && (0 <=? o) && (0 <=? n) && (o + n <? 2 ^ 62) && (0 <=? c) && (c <? 256)) eqn:Hc; [|destruct Hin].
  destruct Hin as [<-|[]].
  apply andb_prop in Hc as [Hc Hc256]. apply andb_prop in Hc as [Hc Hc0]. apply andb_prop in Hc as [Hc H62].
  apply andb_prop in Hc as [Hc Hn0]. apply andb_prop in Hc as [_ Ho0].
  apply Z.leb_le in Ho0, Hn0, Hc0. apply Z.ltb_lt in H62, Hc256.
  destruct HK as (Hflat & Hz). unfold AX2S.elenZ in *. cbn [AX2.edenot] in *.
  rewrite br_lit_small in * by lia.
  destruct (aview_adr a t o _ Hav Hflat ltac:(lia)) as [_ Est].
  cbn [fill_ok]. split; [exact Ho0|]. split; [exact H62|]. split; [lia|].
  intros i Hi. specialize (Hz i Hi). rewrite Est in Hz.
  assert (Ea : Z_to_bv 64 (bv_unsigned (rho t) + o + i) = adr rho t (o + i)).
  { unfold adr. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64). rewrite Zplus_mod_idemp_r. f_equal. lia. }
  rewrite Ea in Hz. apply (rview_full segs H (ms_mem ms) Hnoseg).
  rewrite rview_seg_rom. rewrite Hz. reflexivity.
Qed.

(* [comment removed for export] *)
Definition fill_piece_chk (FC : list (int * Z * Z * Z)) (t off n : int) (w : w64) : bool :=
  existsb (fun q : int * Z * Z * Z => let '(t', o, l, c) := q in
     if (t' =? t)%uint63 then
       (o <=? to_Z off) && (to_Z off + to_Z n <=? o + l) && (to_Z n <=? 8)
       && (wtop w =? wtop (fillw c))%uint63 && (wlo w =? wlo (fillw c))%uint63
     else false) FC.

Lemma fillw_bytes c j : 0 <= c < 256 -> (j < 8)%nat -> nth_error (w_bytes (fillw c)) j = Some (Z_to_bv 8 c).
Proof.
  intros Hc Hj. unfold fillw. cbv zeta.
  assert (Eb : to_Z (of_Z c) = c) by (apply of_Z_small; lia).
  rewrite w_bytes_w_of_bytes8 by (rewrite Eb; lia). rewrite Eb.
  do 8 (destruct j as [|j]; [reflexivity|]). lia.
Qed.

Lemma fill_piece_sound FC t off n w :
  Forall fill_ok FC -> fill_piece_chk FC t off n w = true -> hholds segs rho ms (HCell t off n w).
Proof.
  intros HFC Hc. unfold fill_piece_chk in Hc. apply existsb_exists in Hc as ([[[t' o] l] c] & Hin & Hq).
  destruct (t' =? t)%uint63 eqn:Et; [|discriminate]. apply Uint63.eqb_spec in Et. subst t'.
  apply andb_prop in Hq as [Hq Hlo]. apply andb_prop in Hq as [Hq Htop]. apply andb_prop in Hq as [Hq Hn8].
  apply andb_prop in Hq as [Ho Hhi]. apply Z.leb_le in Ho, Hhi, Hn8. apply Uint63.eqb_spec in Htop, Hlo.
  assert (Ew : w = fillw c) by (destruct w as [wt wl]; destruct (fillw c) as [ft fl] eqn:Ef; cbn [wtop wlo] in Htop, Hlo; subst; reflexivity).
  subst w.
  pose proof (proj1 (Forall_forall _ _) HFC _ Hin) as (Ho0 & H62 & Hc256 & Hfill). cbn [hholds].
  intros j Hj. pose proof (i63_range n) as Hn0. pose proof (i63_range off) as Hoff0.
  assert (Hj8 : (j < 8)%nat) by lia.
  rewrite (fillw_bytes c j Hc256 Hj8).
  replace (to_Z off + Z.of_nat j) with (o + (to_Z off + Z.of_nat j - o)) by lia.
  apply Hfill. lia.
Qed.

(* [comment removed for export] *)
Definition fact_of_reg (regs : list AX2.expr) (i : nat) : option hfact :=
  match vview_ok (nth i regs (AX2.ELit 0)) with
  | Some fv => if (Nat.leb 1 i && Nat.leb i 31)%bool then Some (HReg (of_Z (Z.of_nat i)) fv) else None
  | None => None
  end.

Theorem fact_of_reg_sound regs i f :
  fact_of_reg regs i = Some f ->
  AX2S.regs_ok E regs (ms_regs ms) ->
  hholds segs rho ms f.
Proof.
  unfold fact_of_reg. intros Hf Hregs.
  destruct (vview_ok (nth i regs (AX2.ELit 0))) as [fv|] eqn:Hv; [|discriminate].
  destruct (Nat.leb 1 i && Nat.leb i 31)%bool eqn:Hi; [|discriminate]. injection Hf as <-.
  apply andb_prop in Hi as [H1 H31]. apply Nat.leb_le in H1, H31.
  cbn [hholds]. intros rr Hrr. unfold ireg in Hrr.
  pose proof (bv_unsigned_in_range _ rr) as Hr5. change (bv_modulus 5) with 32 in Hr5.
  assert (Eu : bv_unsigned rr = Z.of_nat i).
  { apply (f_equal to_Z) in Hrr. rewrite !of_Z_small in Hrr by lia. exact Hrr. }
  specialize (Hregs rr). unfold getr, AX2.sr_get in Hregs.
  assert (Hnz : bv_eqb rr 0 = false).
  { unfold bv_eqb. apply Z.eqb_neq. change (bv_unsigned (0 : reg)) with 0. lia. }
  rewrite Hnz in Hregs. unfold Sem.rget. change (is_x0 rr) with (bv_eqb rr 0). rewrite Hnz.
  change (c_regs (core_of ms)) with (ms_regs ms). rewrite Hregs.
  unfold AX2.ridx. rewrite Eu, Nat2Z.id. exact (vview_ok_sound _ _ Hv).
Qed.

End Facts.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Regions.
Variable segs : list Segment.
Variable E : AX2.env.
Variable TT : ttab_e.
Variable kn : list AX2.kentry.
Variable base : word -> option byte.
Hypothesis Hkn : AX2S.know_ok segs E base kn.

Local Notation rho := (rho_of TT E).

(* [comment removed for export] *)
Definition tte (t : int) : AX2.expr :=
  if (t =? 0)%uint63 then AX2.ELit 0 else match tt_get TT t with Some e => e | None => AX2.ELit 0 end.

Lemma rho_tte t : rho t = AX2.edenot E (tte t).
Proof.
  unfold rho_of, tte. destruct (t =? 0)%uint63; [reflexivity|]. destruct (tt_get TT t); reflexivity.
Qed.

Definition region_chk (t lo len al : int) : bool :=
  match AX2.base_range kn (tte t) with
  | Some (blo, bhi) =>
      (to_Z t <? 2 ^ 60) && (to_Z len <=? 2 ^ 62) && (bhi + to_Z len <? 2 ^ 63)
      && ((t =? 0)%uint63 || (0 <? blo + to_Z lo)) && (to_Z al <=? AX2.ealign kn (tte t))
  | None => false
  end.

Theorem region_chk_sound t lo len al :
  region_chk t lo len al = true -> region_ok rho t (RG lo len al None iempty clo_dflt chi_dflt).
Proof.
  unfold region_chk. intros Hc.
  destruct (AX2.base_range kn (tte t)) as [[blo bhi]|] eqn:Hr; [|discriminate].
  apply andb_prop in Hc as [Hc Hal]. apply andb_prop in Hc as [Hc Hpos]. apply andb_prop in Hc as [Hc Hhi].
  apply andb_prop in Hc as [Ht Hlen]. apply Z.ltb_lt in Ht, Hhi. apply Z.leb_le in Hlen, Hal.
  destruct (AX2S.base_range_sound segs E base kn _ blo bhi Hkn Hr) as [Hlo' Hhi'].
  destruct (AX2S.ealign_sound segs E base kn (tte t) Hkn) as [[Ha0 Ha1] Hdiv].
  rewrite <- rho_tte in Hlo', Hhi', Hdiv.
  pose proof (i63_range len) as Hl0. pose proof (i63_range lo) as Hlo0. pose proof (i63_range al) as Hal0.
  pose proof (br_u64 (rho t)) as Hu.
  unfold region_ok. cbn [rg_lo rg_len rg_align rg_clo rg_chi rg_kind].
  change (to_Z clo_dflt) with 0. change (to_Z chi_dflt) with (2 ^ 63 - 1).
  assert (Hmod : bv_unsigned (rho t) mod 2 ^ to_Z al = 0).
  { apply Z.mod_divide; [apply Z.pow_nonzero; lia|].
    apply (Z.divide_trans _ (2 ^ AX2.ealign kn (tte t))); [|exact Hdiv].
    exists (2 ^ (AX2.ealign kn (tte t) - to_Z al)). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
  repeat split; try lia; try exact Hmod; try exact I.
  intros Hne. apply orb_prop in Hpos as [H0|H0].
  - apply Uint63.eqb_spec in H0. contradiction.
  - apply Z.ltb_lt in H0. lia.
Qed.

(* [comment removed for export] *)
Fixpoint chain_apart (ap : Z -> Z -> bool) (x : Z) (cuts : list Z) (y : Z) : bool :=
  match cuts with
  | [] => (x <? y) && ap x y
  | c :: r => (x <? c) && ap x c && chain_apart ap c r y
  end.

Lemma chain_apart_sound (ap : Z -> Z -> bool) (u j0 j1 : Z) :
  j0 < j1 ->
  (forall x y, x < y -> ap x y = true -> u + y <= j0 \/ j1 <= u + x) ->
  forall cuts x y, chain_apart ap x cuts y = true -> x < y /\ (u + y <= j0 \/ j1 <= u + x).
Proof.
  intros Hj Hap. induction cuts as [|c r IH]; intros x y Hc; cbn [chain_apart] in Hc.
  - apply andb_prop in Hc as [Hxy Ha]. apply Z.ltb_lt in Hxy. split; [exact Hxy | exact (Hap x y Hxy Ha)].
  - apply andb_prop in Hc as [Hc Hr]. apply andb_prop in Hc as [Hxc Ha]. apply Z.ltb_lt in Hxc.
    destruct (IH c y Hr) as [Hcy Hd]. pose proof (Hap x c Hxc Ha) as Hd1. split; lia.
Qed.

Definition disj_chk (c1 c2 : list Z) (t1 lo1 len1 t2 lo2 len2 : int) : bool :=
  chain_apart (fun x y =>
    chain_apart (fun x2 y2 => AX2.ranges_apart kn (tte t1) x (y - x) (tte t2) x2 (y2 - x2)) (to_Z lo2) c2 (to_Z len2))
    (to_Z lo1) c1 (to_Z len1).

Theorem disj_chk_sound c1 c2 t1 lo1 len1 t2 lo2 len2 :
  disj_chk c1 c2 t1 lo1 len1 t2 lo2 len2 = true ->
  bv_unsigned (rho t1) + to_Z len1 <= bv_unsigned (rho t2) + to_Z lo2
  \/ bv_unsigned (rho t2) + to_Z len2 <= bv_unsigned (rho t1) + to_Z lo1.
Proof.
  unfold disj_chk. intros Hc.
  (* [comment removed for export] *)
  assert (Hne2 : to_Z lo2 < to_Z len2).
  { destruct c1 as [|c r]; cbn [chain_apart] in Hc.
    - apply andb_prop in Hc as [Hxy Ha].
      set (ap2 := fun x2 y2 => AX2.ranges_apart kn (tte t1) (to_Z lo1) (to_Z len1 - to_Z lo1) (tte t2) x2 (y2 - x2)) in Ha.
      clear Hxy. revert Ha. generalize (to_Z lo2) as x. induction c2 as [|c' r' IH]; intros x Ha; cbn [chain_apart] in Ha.
      + apply andb_prop in Ha as [Hlt _]. apply Z.ltb_lt in Hlt. exact Hlt.
      + apply andb_prop in Ha as [Ha Hr]. apply andb_prop in Ha as [Hlt _]. apply Z.ltb_lt in Hlt.
        specialize (IH c' Hr). lia.
    - apply andb_prop in Hc as [Hc _]. apply andb_prop in Hc as [_ Ha].
      set (ap2 := fun x2 y2 => AX2.ranges_apart kn (tte t1) (to_Z lo1) (c - to_Z lo1) (tte t2) x2 (y2 - x2)) in Ha.
      revert Ha. generalize (to_Z lo2) as x. induction c2 as [|c' r' IH]; intros x Ha; cbn [chain_apart] in Ha.
      + apply andb_prop in Ha as [Hlt _]. apply Z.ltb_lt in Hlt. exact Hlt.
      + apply andb_prop in Ha as [Ha Hr]. apply andb_prop in Ha as [Hlt _]. apply Z.ltb_lt in Hlt.
        specialize (IH c' Hr). lia. }
  refine (proj2 (chain_apart_sound _ (bv_unsigned (rho t1)) (bv_unsigned (rho t2) + to_Z lo2)
                   (bv_unsigned (rho t2) + to_Z len2) ltac:(lia) _ c1 (to_Z lo1) (to_Z len1) Hc)).
  intros x y Hxy Hin.
  refine ((fun Hq => _) (proj2 (chain_apart_sound _ (bv_unsigned (rho t2)) (bv_unsigned (rho t1) + x)
                   (bv_unsigned (rho t1) + y) ltac:(lia) _ c2 (to_Z lo2) (to_Z len2) Hin))); [lia|].
  intros x2 y2 Hxy2 Hra.
  pose proof (AX2S.ranges_apart_sound segs E base kn _ _ _ _ _ _ Hkn Hra) as Hd.
  unfold AX2S.estart in Hd. cbn [AX2.a_base AX2.a_off] in Hd. rewrite <- !rho_tte in Hd. lia.
Qed.

End Regions.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rshape : Type := (int * int * int * int * option pkind)%type.
Definition sh_tag (s : rshape) : int := let '(t, _, _, _, _) := s in t.
Definition sh_lo (s : rshape) : int := let '(_, lo, _, _, _) := s in lo.
Definition sh_len (s : rshape) : int := let '(_, _, len, _, _) := s in len.
Definition sh_al (s : rshape) : int := let '(_, _, _, al, _) := s in al.
Definition sh_region (s : rshape) : region := RG (sh_lo s) (sh_len s) (sh_al s) None iempty clo_dflt chi_dflt.

(* [comment removed for export] *)
