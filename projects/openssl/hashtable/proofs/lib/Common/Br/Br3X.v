(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics Fs State Run.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cfg Require Import ShapeAlgBase ShapeCfg NodesCfg LedgerCfg LazyCfg.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.FX Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxImage FxRun FxRn FxHandoff FxHandoff2 FxLazy FxCellFrame
  FxDrive FxDrive3 FxDrive3N FxDrive3S FxDrive3C FxDrive3D FxDrive3H FxDrive3T FxDrive3O FxDrive3W.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec AsanAcct AxSymExec3 AxSymExec3Sound AxSymRun3 BackingAlgebra.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Cx Require Import CxPlan CxPlanSound CxOpt.
From OSSVerify.Proofs.openssl.hashtable.lib.Common.Br Require Import
  BrEnv BrMem BrLedger BrMain BrRev BrRevLedger BrClass BrRevS BrDress BrGrow BrTrans BrHole Br3Root Br3Ops Br3Leaf Br3Know Br3Trans BrRa Br3HoL.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section LinShadow.
Variable segs : list Segment.
Variable E : AX2.env.
Variable kn : list AX2.kentry.
Variable base : word -> option byte.
Hypothesis Hkn : AX2S.know_ok segs E base kn.

(* [comment removed for export] *)
Fixpoint lin_rng (ts : list (Z * AX2.expr)) : option (Z * Z) :=
  match ts with
  | [] => Some (0, 0)
  | (k, a) :: r =>
      match AX2.base_range kn a, lin_rng r with
      | Some (lo, hi), Some (l, h) => Some (l + Z.min (k * lo) (k * hi), h + Z.max (k * lo) (k * hi))
      | _, _ => None
      end
  end.

Lemma lin_rng_sound : forall ts l h, lin_rng ts = Some (l, h) -> l <= AX2S.tden E ts <= h.
Proof.
  induction ts as [|[k a] r IH]; intros l h Hr; cbn [lin_rng AX2S.tden] in *.
  - injection Hr as <- <-. lia.
  - destruct (AX2.base_range kn a) as [[lo hi]|] eqn:Ha; [|discriminate].
    destruct (lin_rng r) as [[l0 h0]|] eqn:Hr0; [|discriminate]. injection Hr as <- <-.
    specialize (IH _ _ eq_refl).
    destruct (AX2S.base_range_sound segs E base kn a lo hi Hkn Ha) as [A1 A2]. unfold AX2S.uE.
    set (u := bv_unsigned (AX2.edenot E a)) in *.
    assert (Hm : Z.min (k * lo) (k * hi) <= k * u <= Z.max (k * lo) (k * hi)).
    { destruct (Z.le_gt_cases 0 k); [assert (k * lo <= k * u <= k * hi) by nia | assert (k * hi <= k * u <= k * lo) by nia]; lia. }
    lia.
Qed.

Definition div8_terms (ts : list (Z * AX2.expr)) : list (Z * AX2.expr) := map (fun t => (fst t / 8, snd t)) ts.

Lemma tden_div8 : forall ts, forallb (fun t : Z * AX2.expr => fst t mod 8 =? 0) ts = true ->
  AX2S.tden E ts = 8 * AX2S.tden E (div8_terms ts).
Proof.
  induction ts as [|[k a] r IH]; intros Hc; cbn [forallb div8_terms map AX2S.tden fst snd] in *; [reflexivity|].
  apply andb_prop in Hc as [H1 H2]. apply Z.eqb_eq in H1. fold (div8_terms r). rewrite (IH H2).
  assert (k = 8 * (k / 8)) by (clear - H1; Z.div_mod_to_equations; lia). nia.
Qed.

(* [comment removed for export] *)
Definition lin_sh_chk (ep et : AX2.expr) : bool :=
  let lp := AX2.lin_of ep in
  (fst lp mod 8 =? 0) && forallb (fun t : Z * AX2.expr => fst t mod 8 =? 0) (snd lp)
  && match lin_rng (snd lp) with
     | Some (lo, hi) => (0 <=? fst lp + lo) && (fst lp + hi <? 2 ^ 64)
     | None => false
     end
  && lin_match (AX2.lin_of et) (fst lp / 8 + to_Z shadow_K, div8_terms (snd lp)) 0.

Lemma lin_sh_sound ep et : lin_sh_chk ep et = true ->
  bv_unsigned (AX2.edenot E et) = bv_unsigned (AX2.edenot E ep) / 8 + to_Z shadow_K.
Proof.
  unfold lin_sh_chk. cbv zeta. intros Hc.
  apply andb_prop in Hc as [Hc Hm]. apply andb_prop in Hc as [Hc Hr]. apply andb_prop in Hc as [Hc8 Ht8].
  apply Z.eqb_eq in Hc8.
  destruct (lin_rng (snd (AX2.lin_of ep))) as [[lo hi]|] eqn:Hrng; [|discriminate].
  apply andb_prop in Hr as [R1 R2]. apply Z.leb_le in R1. apply Z.ltb_lt in R2.
  pose proof (lin_rng_sound _ _ _ Hrng) as Hb.
  pose proof (AX2S.lin_of_sound E ep) as Hp. pose proof (AX2S.lin_of_sound E et) as Ht.
  pose proof (lin_match_sound E _ _ _ Hm) as Hq.
  pose proof (tden_div8 _ Ht8) as H8.
  unfold AX2S.lden in *. cbn [fst snd] in Hq.
  set (c := fst (AX2.lin_of ep)) in *. set (S8 := AX2S.tden E (div8_terms (snd (AX2.lin_of ep)))) in *.
  change (to_Z shadow_K) with 2147450880 in *.
  pose proof (br_u64 (AX2.edenot E ep)) as Hup. pose proof (br_u64 (AX2.edenot E et)) as Hut.
  assert (Ep : c + AX2S.tden E (snd (AX2.lin_of ep)) = bv_unsigned (AX2.edenot E ep)).
  { apply br_eqm_small; [exact Hp | lia | exact Hup]. }
  assert (Ediv : bv_unsigned (AX2.edenot E ep) / 8 = c / 8 + S8).
  { rewrite <- Ep, H8. clear - Hc8. Z.div_mod_to_equations. lia. }
  rewrite Ediv. apply br_eqm_small; [|exact Hut|].
  - destruct Ht as [q1 H1]. destruct Hq as [q2 H2]. exists (q2 - q1). unfold AX2S.uE in *. lia.
  - assert (0 <= c / 8 + S8 < 2 ^ 61) by (rewrite <- Ediv; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]). lia.
Qed.

End LinShadow.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section DressL.
Variable segs : list Segment.
Variable E : AX2.env.
Variable TT : ttab_e.
Variable kn : list AX2.kentry.
Variable base : word -> option byte.
Hypothesis Hkn : AX2S.know_ok segs E base kn.
Variable n : int.
Variable ORD : list (int * int * Z).

Local Notation rho := (rho_of TT E).

(* [comment removed for export] *)
Definition lo_by_ord (t : int) (clo : Z) : bool :=
  existsb (fun o : int * int * Z =>
     let '(ta, tb, dd) := o in
     (tb =? t)%uint63
     && match AX2.base_range kn (tte TT ta) with Some (alo, _) => (clo <=? alo + dd) | None => false end
     && CAP.xinsideJ kn (tte TT t) 0 (AX2.ELit 1) (tte TT ta) dd (AX2.ELit (2 ^ 62))) ORD.

Lemma lo_by_ord_sound t clo : lo_by_ord t clo = true -> clo <= bv_unsigned (rho t).
Proof.
  unfold lo_by_ord. intros Hc. apply existsb_exists in Hc as ([[ta tb] dd] & _ & Hc).
  apply andb_prop in Hc as [Hc Hx]. apply andb_prop in Hc as [_ Hb].
  destruct (AX2.base_range kn (tte TT ta)) as [[alo ahi]|] eqn:Ra; [|discriminate]. apply Z.leb_le in Hb.
  destruct (AX2S.base_range_sound segs E base kn _ alo ahi Hkn Ra) as [A1 _]. rewrite <- (rho_tte E TT ta) in A1.
  destruct (CXS.xinsideJ_sound segs E base kn _ _ _ _ _ _ Hkn Hx) as [X1 _].
  unfold AX2S.estart in X1. cbn [AX2.a_base AX2.a_off] in X1. rewrite <- !(rho_tte E TT) in X1. lia.
Qed.

Definition dress_chkL (x : ditem) : bool :=
  let '(t, clo, chi, k) := x in
  (to_Z t <? to_Z n)
  && match AX2.base_range kn (tte TT t) with
     | Some (blo, bhi) => (if (to_Z clo <=? blo) then true else lo_by_ord t (to_Z clo)) && (bhi <=? to_Z chi)
     | None => false
     end
  && match k with
     | RK_plain => true
     | RK_shadow p => (to_Z p <? to_Z t)
                      && (if AX2.expr_eqb (tte TT t) (shadow_e (tte TT p)) then true else lin_sh_chk kn (tte TT p) (tte TT t))
     end.

Lemma dress_chkL_sound x : dress_chkL x = true -> ditem_lt n x /\ ditem_ok rho x.
Proof.
  destruct x as [[[t clo] chi] k]. unfold dress_chkL. intros Hc.
  apply andb_prop in Hc as [Hc Hk]. apply andb_prop in Hc as [Ht Hb]. apply Z.ltb_lt in Ht.
  destruct (AX2.base_range kn (tte TT t)) as [[blo bhi]|] eqn:Hr; [|discriminate].
  apply andb_prop in Hb as [Hb1 Hb2]. apply Z.leb_le in Hb2.
  destruct (AX2S.base_range_sound segs E base kn _ blo bhi Hkn Hr) as [Hlo Hhi].
  rewrite <- (rho_tte E TT t) in Hlo, Hhi.
  assert (Hclo : to_Z clo <= bv_unsigned (rho t)).
  { destruct (to_Z clo <=? blo) eqn:Ec; [apply Z.leb_le in Ec; lia | exact (lo_by_ord_sound t _ Hb1)]. }
  destruct k as [|p].
  - split; cbn [ditem_lt ditem_ok rkind_ok]; repeat split; try exact I; lia.
  - apply andb_prop in Hk as [Hp He]. apply Z.ltb_lt in Hp.
    split; cbn [ditem_lt ditem_ok rkind_ok]; repeat split; try lia.
    destruct (AX2.expr_eqb (tte TT t) (shadow_e (tte TT p))) eqn:Eq.
    + apply AX2S.expr_eqb_eq in Eq. rewrite (rho_tte E TT t), Eq, shadow_e_den, <- (rho_tte E TT p). reflexivity.
    + rewrite (rho_tte E TT t), (rho_tte E TT p). exact (lin_sh_sound segs E kn base Hkn _ _ He).
Qed.

Lemma dress_chkL_all bs : forallb dress_chkL bs = true -> Forall (ditem_lt n) bs /\ Forall (ditem_ok rho) bs.
Proof.
  intros Hc. rewrite forallb_forall in Hc. split; apply Forall_forall; intros x Hx; destruct (dress_chkL_sound x (Hc x Hx)); assumption.
Qed.

End DressL.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section XFacts.
Variable segs : list Segment.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Variable E : AX2.env.
Variable CS : CAP.acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
Hypothesis Hlx : CxOpt.ledger_exact E (CAP.a_maps CS).     (* [comment removed for export] *)
Let Hnf : CAP.no_fog (CAP.a_maps CS) = true := CxOpt.ledger_exact_nf _ _ Hlx.
Variable TT : ttab_e.
Variable RF : list hfact.          (* [comment removed for export] *)

Local Notation rho := (rho_of TT E).
Local Notation kn := (CAP.kn CS).
Local Notation ms := (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)).
Hypothesis HRF : Forall (hholds segs rho ms) RF.
(* [comment removed for export] *)
Variable FC : list (int * Z * Z * Z).
Hypothesis HFC : Forall (fill_ok segs E TT ms) FC.
(* [comment removed for export] *)
Variable bs : list ditem.
Hypothesis Hdok : Forall (ditem_ok rho) bs.

Definition xf_bnd (p : int) : option (Z * Z) :=
  match List.find (fun it : ditem => let '(t, _, _, _) := it in (t =? p)%uint63) bs with
  | Some (_, clo, chi, _) => Some (to_Z clo, to_Z chi)
  | None => AX2.base_range kn (tte TT p)
  end.

Lemma xf_bnd_sound p blo bhi : xf_bnd p = Some (blo, bhi) -> blo <= bv_unsigned (rho p) <= bhi.
Proof.
  unfold xf_bnd. destruct (List.find (fun it : ditem => let '(t, _, _, _) := it in (t =? p)%uint63) bs) as [[[[t clo] chi] k]|] eqn:Hf.
  - intros Hb. injection Hb as <- <-. apply find_some in Hf as [Hin Ht]. apply Uint63.eqb_spec in Ht. subst t.
    pose proof (proj1 (Forall_forall _ _) Hdok _ Hin) as Hok. cbn [ditem_ok] in Hok. exact (proj1 Hok).
  - intros Hbr. pose proof (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hkn.
    destruct (AX2S.base_range_sound segs E _ kn _ blo bhi Hkn Hbr) as [H1 H2]. rewrite <- (rho_tte E TT p) in H1, H2. lia.
Qed.

Definition par_disj (p1 : int) (a1 b1 : Z) (p2 : int) (a2 b2 : Z) : bool :=
  existsb (fun f => match f with
     | HDisj u1 l1 n1 u2 l2 n2 =>
         ((u1 =? p1)%uint63 && (u2 =? p2)%uint63 && (to_Z l1 <=? a1) && (b1 <=? to_Z n1) && (to_Z l2 <=? a2) && (b2 <=? to_Z n2))
         || ((u1 =? p2)%uint63 && (u2 =? p1)%uint63 && (to_Z l1 <=? a2) && (b2 <=? to_Z n1) && (to_Z l2 <=? a1) && (b1 <=? to_Z n2))
     | _ => false
     end) RF.

(* [comment removed for export] *)
Definition xf_chk (f : hfact) : bool :=
  match f with
  | HZero t off len | HWr t off len =>
      let p := (t - 1)%uint63 in
      lin_sh_chk kn (tte TT p) (tte TT t)
      && match xf_bnd p with
         | Some (blo, bhi) => zsh_chkB A CS TT p (8 * to_Z off) (8 * (to_Z off + to_Z len)) blo bhi
         | None => false
         end
  | HDisj t1 lo1 len1 t2 lo2 len2 =>
      let p1 := (t1 - 1)%uint63 in let p2 := (t2 - 1)%uint63 in
      lin_sh_chk kn (tte TT p1) (tte TT t1) && lin_sh_chk kn (tte TT p2) (tte TT t2)
      && (3 <=? AX2.ealign kn (tte TT p1)) && (3 <=? AX2.ealign kn (tte TT p2))
      && par_disj p1 (8 * to_Z lo1) (8 * to_Z len1) p2 (8 * to_Z lo2) (8 * to_Z len2)
  | HCell t off n w => fill_piece_chk FC t off n w      (* [comment removed for export] *)
  | _ => false
  end.

Lemma xf_kind p t : lin_sh_chk kn (tte TT p) (tte TT t) = true ->
  bv_unsigned (rho t) = bv_unsigned (rho p) / 8 + to_Z shadow_K.
Proof.
  intros Hc. rewrite (rho_tte E TT t), (rho_tte E TT p).
  exact (lin_sh_sound segs E kn _ (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) _ _ Hc).
Qed.

Lemma xf_zone t off len : 
  lin_sh_chk kn (tte TT (t - 1)%uint63) (tte TT t) = true ->
  match xf_bnd (t - 1)%uint63 with
  | Some (blo, bhi) => zsh_chkB A CS TT (t - 1)%uint63 (8 * to_Z off) (8 * (to_Z off + to_Z len)) blo bhi
  | None => false
  end = true ->
  forall j, 0 <= j < to_Z len ->
    rview segs FULL (adr rho t (to_Z off + j)) = Some (Z_to_bv 8 0) /\ wview segs FULL (adr rho t (to_Z off + j)) <> None.
Proof.
  intros Hk Hz j Hj. pose proof (xf_kind _ _ Hk) as Ek.
  destruct (xf_bnd (t - 1)%uint63) as [[blo bhi]|] eqn:Hbn; [|discriminate]. pose proof (xf_bnd_sound _ _ _ Hbn) as Hbnd.
  destruct (zsh_chkB_bounds A E CS TT _ _ _ _ _ Hz Hbnd) as (B1 & B2 & B3).
  pose proof (br_u64 (rho (t - 1)%uint63)) as Hu. pose proof (i63_range off) as Ho.
  change (to_Z shadow_K) with 2147450880 in Ek.
  assert (Hq : 0 <= bv_unsigned (rho (t - 1)%uint63) / 8 < 2 ^ 61)
    by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Ea : bv_unsigned (adr rho t (to_Z off + j)) = bv_unsigned (rho t) + (to_Z off + j)).
  { apply adr_unsigned; lia. }
  apply (zsh_zeroB segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT _ _ _ _ _ Hz Hbnd).
  rewrite Ea, Ek. change (to_Z shadow_K) with 2147450880.
  replace (8 * to_Z off / 8) with (to_Z off) by (rewrite Z.mul_comm, Z.div_mul; lia).
  replace (8 * (to_Z off + to_Z len) / 8) with (to_Z off + to_Z len) by (rewrite Z.mul_comm, Z.div_mul; lia). lia.
Qed.

Theorem xf_chk_sound f : xf_chk f = true -> hholds segs rho ms f.
Proof.
  destruct f as [tc offc nc wc | | | t off len | | t off len | | | t1 lo1 len1 t2 lo2 len2]; cbn [xf_chk]; try discriminate; intros Hc.
  - exact (fill_piece_sound segs E TT ms FC tc offc nc wc HFC Hc).
  - apply andb_prop in Hc as [Hk Hz]. cbn [hholds ms_mem PropExec.mkst]. intros j Hj. exact (proj1 (xf_zone t off len Hk Hz j Hj)).
  - apply andb_prop in Hc as [Hk Hz]. cbn [hholds ms_mem PropExec.mkst]. intros j Hj. exact (proj2 (xf_zone t off len Hk Hz j Hj)).
  - cbv zeta in Hc. apply andb_prop in Hc as [Hc Hpd]. apply andb_prop in Hc as [Hc Ha2]. apply andb_prop in Hc as [Hc Ha1].
    apply andb_prop in Hc as [Hk1 Hk2]. apply Z.leb_le in Ha1, Ha2.
    pose proof (xf_kind _ _ Hk1) as E1. pose proof (xf_kind _ _ Hk2) as E2.
    pose proof (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hkn.
    destruct (AX2S.ealign_sound segs E _ kn (tte TT (t1 - 1)%uint63) Hkn) as [_ D1]. rewrite <- (rho_tte E TT) in D1.
    destruct (AX2S.ealign_sound segs E _ kn (tte TT (t2 - 1)%uint63) Hkn) as [_ D2]. rewrite <- (rho_tte E TT) in D2.
    pose proof (br_u64 (rho (t1 - 1)%uint63)) as Hu1. pose proof (br_u64 (rho (t2 - 1)%uint63)) as Hu2.
    destruct (div8_facts (bv_unsigned (rho (t1 - 1)%uint63)) 0 _ ltac:(lia) ltac:(lia) Ha1 D1) as [M1 _].
    destruct (div8_facts (bv_unsigned (rho (t2 - 1)%uint63)) 0 _ ltac:(lia) ltac:(lia) Ha2 D2) as [M2 _].
    unfold par_disj in Hpd. apply existsb_exists in Hpd as (g & Hg & Hm).
    pose proof (proj1 (Forall_forall _ _) HRF g Hg) as Hh.
    destruct g as [| | | | | | | | u1 l1 n1 u2 l2 n2]; try discriminate. cbn [hholds] in Hh |- *.
    rewrite E1, E2. set (r1 := bv_unsigned (rho (t1 - 1)%uint63)) in *. set (r2 := bv_unsigned (rho (t2 - 1)%uint63)) in *.
    apply orb_prop in Hm as [Hm|Hm];
      repeat (apply andb_prop in Hm as [Hm ?]);
      repeat match goal with H : (_ =? _)%uint63 = true |- _ => apply Uint63.eqb_spec in H | H : (_ <=? _) = true |- _ => apply Z.leb_le in H end;
      subst u1 u2; fold r1 r2 in Hh; clear - Hh M1 M2 H H0 H1 H2; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Definition xf_chkP (ra : ra_t) (pre : bool) (f : hfact) : bool :=
  match f with
  | HZero t off len | HWr t off len =>
      let p := (t - 1)%uint63 in
      lin_sh_chk kn (tte TT p) (tte TT t)
      && match xf_bnd p with
         | Some (blo, bhi) => zsh_chkPR A CS TT ra pre p (8 * to_Z off) (8 * (to_Z off + to_Z len)) blo bhi
         | None => false
         end
  | _ => xf_chk f
  end.
Lemma xf_chkP_eq ra f : ra = AX2.ranges_apart kn -> xf_chkP ra (zsh_pre A CS) f = xf_chk f.
Proof.
  intros Hra. destruct f; try reflexivity; cbn [xf_chkP xf_chk]; cbv zeta;
    destruct (xf_bnd (t - 1)%uint63) as [[blo bhi]|]; try reflexivity; rewrite (zsh_chkPR_eq A CS TT ra _ _ _ _ _ Hra); reflexivity.
Qed.

Definition xf_key (f : hfact) : option (int * int * int) :=
  match f with HZero t off len | HWr t off len => Some (t, off, len) | _ => None end.
Definition xf_same (f : hfact) (last : option (int * int * int)) : bool :=
  match xf_key f, last with
  | Some (t, o, l), Some (t', o', l') => if (t =? t')%uint63 then if (o =? o')%uint63 then (l =? l')%uint63 else false else false
  | _, _ => false
  end.
Fixpoint xf_allP (ra : ra_t) (pre : bool) (last : option (int * int * int)) (l : list hfact) : bool :=
  match l with
  | [] => true
  | f :: r => if (if xf_same f last then true else xf_chkP ra pre f) then xf_allP ra pre (xf_key f) r else false
  end.
Definition xf_all (XF : list hfact) : bool :=
  let ra := ra_fast kn in let pre := zsh_pre A CS in xf_allP ra pre None XF.

Lemma xf_key_chk f g : xf_key f = xf_key g -> xf_key f <> None -> xf_chk f = xf_chk g.
Proof.
  destruct f, g; cbn [xf_key]; intros Hk Hn; try discriminate Hk; try (exfalso; apply Hn; reflexivity);
    injection Hk as -> -> ->; reflexivity.
Qed.

Lemma xf_allP_ok ra : ra = AX2.ranges_apart kn -> forall l last,
  (forall f, xf_key f = last -> last <> None -> xf_chk f = true) ->
  xf_allP ra (zsh_pre A CS) last l = true -> forallb xf_chk l = true.
Proof.
  intros Hra. induction l as [|f r IH]; intros last Hlast Hc; cbn [xf_allP forallb] in *; [reflexivity|].
  assert (Hf : xf_chk f = true).
  { destruct (xf_same f last) eqn:Es.
    - unfold xf_same in Es. destruct (xf_key f) as [[[t o] l]|] eqn:Ek; [|discriminate]. destruct last as [[[t' o'] l']|]; [|discriminate].
      destruct (t =? t')%uint63 eqn:E1; [|discriminate]. destruct (o =? o')%uint63 eqn:E2; [|discriminate].
      apply Uint63.eqb_spec in E1, E2, Es. subst t' o' l'. apply Hlast; [exact Ek | discriminate].
    - rewrite (xf_chkP_eq ra f Hra) in Hc. destruct (xf_chk f); [reflexivity | discriminate Hc]. }
  rewrite Hf. cbn [andb]. apply (IH (xf_key f)).
  - intros g Hg Hn. rewrite (xf_key_chk g f Hg ltac:(rewrite Hg; exact Hn)). exact Hf.
  - destruct (if xf_same f last then true else xf_chkP ra (zsh_pre A CS) f); [exact Hc | discriminate Hc].
Qed.

Lemma xf_all_ok XF : xf_all XF = true -> forallb xf_chk XF = true.
Proof. unfold xf_all. cbv zeta. apply (xf_allP_ok _ (ra_fast_eq kn)). intros f _ Hn. exfalso. apply Hn. reflexivity. Qed.

End XFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section SideX.
Variable segs : list Segment.
Variable IM : fimage.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : CXS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variable E : AX2.env.
Variable CS : CAP.acs.
Variable R : bvmap 5 word.
Variable FULL : word -> option byte.
Variable m : Model.
Hypothesis HCS : CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m.
Hypothesis Hlx : CxOpt.ledger_exact E (CAP.a_maps CS).     (* [comment removed for export] *)
Let Hnf : CAP.no_fog (CAP.a_maps CS) = true := CxOpt.ledger_exact_nf _ _ Hlx.
Variable TT : ttab_e.
Hypothesis HTT : tt_wf TT = true.
Variable d : sdesc.
Variable bs : list ditem.
Variable XA : list fent.

Local Notation rho := (rho_of TT E).
Local Notation M0 := (f_mem (state_of d)).
Local Notation kn := (CAP.kn CS).
Local Notation H := (CXS.hid A argH E CS m).
Local Notation V := (m_vmmaps m).
Hypothesis Hdok : Forall (ditem_ok rho) bs.
Hypothesis Hmem0 : mem_ok segs IM rho M0 FULL.

(* [comment removed for export] *)
Definition shvis_q (p : int) (lo len : Z) (q : AX2.expr * AX2.expr) : bool :=
  CAP.xinsideJ kn (tte TT p) (8 * lo) (AX2.ELit (8 * (len - lo))) (fst q) 0 (snd q)
  && zapart CS q
  && match AX2.base_range kn (fst q), len_hi kn (snd q) with
     | Some (_, bhi), Some h => (bhi + h <=? 2 ^ 47)
     | _, _ => false
     end.

Definition shvis_chk (r : rdesc) : bool :=
  (0 <=? to_Z (rd_lo r)) && (to_Z (rd_lo r) <=? to_Z (rd_len r)) && (8 * to_Z (rd_len r) <? 2 ^ 62)
  && existsb (fun it : ditem => let '(t, _, _, k) := it in
       (* [comment removed for export] *)
       if (t =? rd_tag r)%uint63 then
          match k with
          | RK_shadow p => existsb (shvis_q p (to_Z (rd_lo r)) (to_Z (rd_len r))) (CAP.a_vis CS)
          | RK_plain => false
          end
       else false) bs.

(* [comment removed for export] *)
Definition xa_page_in (r : rdesc) (p : pdesc) : bool :=
  existsb (fun e : fent => let '(t, o, l) := e in
             (t =? rd_tag r)%uint63 && (to_Z o <=? to_Z (pd_pn p) * 4096)
             && (to_Z (pd_pn p) * 4096 + 4096 <=? to_Z o + to_Z l)) XA.

Definition xa_pages_chk (r : rdesc) : bool :=
  match rd_dflt r with
  | None => negb (rd_tag r =? 0)%uint63
            && forallb (fun p : pdesc =>
                 if xa_page_in r p then true
                 else pd_wr p && (to_Z (pd_pn p) * 4096 + 4096 <=? to_Z (rd_len r))
                      && vis_root kn M0 (xt_of TT) (rd_tag r) (to_Z (pd_pn p) * 4096) 4096) (rd_pages r)
  | Some _ => false
  end.

Definition region_side_chkX (r : rdesc) : bool :=
  if shvis_chk r then true else if xa_pages_chk r then true else region_side_chk A TT kn d r.

Definition side_chkX : bool :=
  (CAP.shadow_off A =? to_Z shadow_K) && zones_chk CS && forallb region_side_chkX (sd_mem d).

(* [comment removed for export] *)
Definition xa_pages_chkP (cov : list (int * Z * Z)) (r : rdesc) : bool :=
  match rd_dflt r with
  | None => negb (rd_tag r =? 0)%uint63
            && forallb (fun p : pdesc =>
                 if xa_page_in r p then true
                 else pd_wr p && (to_Z (pd_pn p) * 4096 + 4096 <=? to_Z (rd_len r))
                      && vis_pre cov (rd_tag r) (to_Z (pd_pn p) * 4096) 4096) (rd_pages r)
  | Some _ => false
  end.
Lemma xa_pages_chkP_ok r : xa_pages_chkP (root_cov kn M0 (xt_of TT)) r = true -> xa_pages_chk r = true.
Proof.
  unfold xa_pages_chkP, xa_pages_chk. destruct (rd_dflt r); [intros Hc; exact Hc|]. intros Hc.
  apply andb_prop in Hc as [H1 H2]. rewrite H1. cbn [andb]. apply forallb_forall. intros p Hp.
  rewrite forallb_forall in H2. pose proof (H2 p Hp) as H3. destruct (xa_page_in r p); [reflexivity|].
  apply andb_prop in H3 as [H4 H5]. rewrite H4. cbn [andb]. exact (vis_pre_root kn M0 (xt_of TT) _ _ _ H5).
Qed.

(* [comment removed for export] *)
Definition region_side_chkXP (cov : list (int * Z * Z)) (r : rdesc) : bool :=
  if shvis_chk r then true else if xa_pages_chkP cov r then true else region_side_chkP A cov r.
Definition side_chkXP : bool :=
  let cov := root_cov kn (f_mem (state_of d)) (xt_of TT) in
  (CAP.shadow_off A =? to_Z shadow_K) && zones_chk CS && forallb (region_side_chkXP cov) (sd_mem d).
Lemma side_chkXP_ok : side_chkXP = true -> side_chkX = true.
Proof.
  unfold side_chkXP, side_chkX. cbv zeta. intros Hc. apply andb_prop in Hc as [Hc Hall]. rewrite Hc. cbn [andb].
  apply forallb_forall. intros r Hr. rewrite forallb_forall in Hall. pose proof (Hall r Hr) as H1.
  unfold region_side_chkXP in H1. unfold region_side_chkX. destruct (shvis_chk r); [reflexivity|].
  destruct (xa_pages_chkP (root_cov kn (f_mem (state_of d)) (xt_of TT)) r) eqn:Exp; [rewrite (xa_pages_chkP_ok r Exp); reflexivity|].
  destruct (xa_pages_chk r); [reflexivity|]. exact (region_side_chkP_ok A TT kn d r H1).
Qed.

Lemma sx_noseg : forall x, H x = true -> find_segment segs (bv_unsigned x) 1 = None.
Proof. exact (CXS.H_off_segments_cs segs A SEGS_in_hull HULL_ok argH ISP argH_high E CS m). Qed.

Lemma sx_hull : forall a, CAP.img_lo A <= a < CAP.img_hi A -> H (Z_to_bv 64 a) = false.
Proof. exact (fun a => rb_hull A argH ISP HULL_ok argH_high CS E m a). Qed.

Lemma sx_M0 : forall t rg, iget t M0 = Some rg -> region_ok rho t rg.
Proof. intros t rg Hg. exact (proj1 (proj1 Hmem0 t rg Hg)). Qed.

(* [comment removed for export] *)
Lemma sx_zone_vis (x : word) : zones_chk CS = true -> in_shadow (bv_unsigned x) ->
  CXS.in_allow A E CS (bv_unsigned x) = true -> H x = false.
Proof.
  intros Hz Hin Hal. set (z := bv_unsigned x) in *.
  destruct (zones_facts segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx Hz x Hin) as (Hm0 & Hn0 & _). fold z in Hm0, Hn0.
  unfold CXS.hid. apply orb_false_iff. split.
  - apply not_true_is_false. intros Ha. destruct (argH_high E x Ha) as [_ Hisp]. fold z in Hisp.
    apply in_ivs_true in Hm0 as (p' & Hp' & Hzp').
    pose proof (proj1 (Forall_forall _ _) (CXS.co_bounds _ _ _ _ _ _ _ _ _ _ _ _ HCS) _ Hp') as (_ & _ & _ & _ & Hhi).
    destruct (CXS.co_isp _ _ _ _ _ _ _ _ _ _ _ _ HCS) as [Eisp _].
    unfold alloc_top, stack_max_size in Hhi. rewrite Eisp in Hhi. unfold e_hi, e_lo, e_sz in Hzp'. lia.
  - apply negb_false_iff. unfold CXS.vis. cbv zeta. fold z. rewrite Hm0, Hn0, Hal. cbn [negb andb]. rewrite !orb_true_r. reflexivity.
Qed.

Lemma shvis_sound t rg r : iget t M0 = Some rg -> rd_tag r = t -> rg = region_of r ->
  (CAP.shadow_off A =? to_Z shadow_K) = true -> zones_chk CS = true -> shvis_chk r = true ->
  forall off, to_Z (rd_lo r) <= off < to_Z (rd_len r) -> H (adr rho t off) = false.
Proof.
  intros Hg Et Erg HK Hz Hc off Hoff. apply Z.eqb_eq in HK. unfold shvis_chk in Hc.
  apply andb_prop in Hc as [Hc Hex]. apply andb_prop in Hc as [Hc H62]. apply andb_prop in Hc as [Hlo0 Hlole].
  apply Z.leb_le in Hlo0, Hlole. apply Z.ltb_lt in H62.
  apply existsb_exists in Hex as ([[[t' clo] chi] k] & Hit & Hic). apply andb_prop in Hic as [Ht' Hk].
  apply Uint63.eqb_spec in Ht'. subst t'. destruct k as [|p]; [discriminate|].
  apply existsb_exists in Hk as (q & Hq & Hqc). unfold shvis_q in Hqc.
  apply andb_prop in Hqc as [Hqc Htop]. apply andb_prop in Hqc as [Hx Hza].
  pose proof (proj1 (Forall_forall _ _) Hdok _ Hit) as Hok. cbn [ditem_ok] in Hok. destruct Hok as [_ Hkind].
  cbn [rkind_ok] in Hkind. destruct Hkind as [_ Ebase]. rewrite Et in Ebase.
  pose proof (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) as Hkn.
  destruct (CXS.xinsideJ_sound segs E _ kn _ _ _ _ _ _ Hkn Hx) as [X1 X2].
  unfold AX2S.estart, AX2S.elenZ in X1, X2. cbn [AX2.a_base AX2.a_off AX2.edenot] in X1, X2.
  rewrite <- (rho_tte E TT p) in X1, X2.
  rewrite (br_lit_small (8 * (to_Z (rd_len r) - to_Z (rd_lo r)))) in X2 by lia.
  destruct (AX2.base_range kn (fst q)) as [[blo bhi]|] eqn:Hbr; [|discriminate].
  destruct (len_hi kn (snd q)) as [h|] eqn:Hlh; [|discriminate]. apply Z.leb_le in Htop.
  destruct (AX2S.base_range_sound segs E _ kn _ blo bhi Hkn Hbr) as [_ Hbhi].
  pose proof (len_hi_sound segs E kn _ _ Hkn (snd q) h Hlh) as Hh. unfold AX2S.elenZ in Hh.
  destruct (sx_M0 t rg Hg) as (_ & _ & Hb63 & _). rewrite Erg in Hb63. cbn [region_of rg_len] in Hb63.
  pose proof (br_u64 (rho t)) as Hut. pose proof (br_u64 (rho p)) as Hup.
  assert (Ea : bv_unsigned (adr rho t off) = bv_unsigned (rho t) + off) by (apply adr_unsigned; lia).
  set (y := bv_unsigned (rho p) + 8 * off).
  assert (Hy : bv_unsigned (AX2.edenot E (fst q)) <= y < bv_unsigned (AX2.edenot E (fst q)) + bv_unsigned (AX2.edenot E (snd q))) by (unfold y; lia).
  assert (Ey : y / 8 = bv_unsigned (rho p) / 8 + off) by (unfold y; rewrite (Z.mul_comm 8 off), Z.div_add by lia; reflexivity).
  change (to_Z shadow_K) with 2147450880 in *.
  assert (Ez : bv_unsigned (adr rho t off) = y / 8 + 2147450880) by (rewrite Ea, Ebase, Ey; lia).
  apply (sx_zone_vis _ Hz).
  - (* [comment removed for export] *)
    rewrite Ez.
    assert (Hside : y < span_lo \/ span_hi <= y).
    { destruct (Z_lt_dec y span_lo) as [?|Hge]; [left; assumption|]. right.
      destruct (Z_le_dec span_hi y) as [?|Hlt]; [assumption|]. exfalso.
      exact (zapart_span segs A Lim SINV argH ISP FS0 E CS R FULL m HCS q y Hza ltac:(lia) Hy). }
    unfold in_shadow, lsh_lo, lsh_hi, hsh_lo, hsh_hi, span_lo, span_hi in *.
    assert (Hy0 : 0 <= y) by (unfold y; lia).
    destruct Hside as [Hs|Hs]; [left | right]; clear - Hs Hy0 Hy Hbhi Hh Htop; Z.div_mod_to_equations; lia.
  - (* [comment removed for export] *)
    unfold CXS.in_allow. apply orb_true_iff. right. unfold CXS.in_sh. apply existsb_exists. exists q. split; [exact Hq|].
    unfold CXS.sh_lo, CXS.sh_hi, CXS.uE. rewrite HK, Ez. change (to_Z shadow_K) with 2147450880.
    assert (Hy8 : y + 8 <= bv_unsigned (AX2.edenot E (fst q)) + bv_unsigned (AX2.edenot E (snd q))) by (unfold y; lia).
    apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; clear - Hy Hy8; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Lemma page_classX t rg pn p : side_chkX = true ->
  iget t M0 = Some rg -> to_Z pn < 2 ^ 50 -> page_at IM rg t pn = Some p ->
  (forall x, 0 <= x < 4096 -> to_Z pn * 4096 + x < to_Z (rg_len rg) -> H (adr rho t (to_Z pn * 4096 + x)) = false)
  \/ (pg_wr p = false /\ bv_unsigned (rho t) mod 4096 = 0
      /\ exists x, 0 <= x < 4096 /\ H (adr rho t (to_Z pn * 4096 + x)) = false)
  \/ (forall x, 0 <= x < 4096 -> xain rho XA (bv_unsigned (adr rho t (to_Z pn * 4096 + x))) = true).
Proof.
  intros Hside Hg Hpn Hp. unfold side_chkX in Hside. apply andb_prop in Hside as [Hside Hall]. apply andb_prop in Hside as [HK Hz].
  destruct (proj1 Hmem0 t rg Hg) as [Hrok Hpages]. destruct (Hpages pn p Hpn Hp) as (_ & Hlo & Hlt & _).
  pose proof Hg as Hg2. cbn [state_of f_mem] in Hg2.
  destruct (iget_iof_list_map_In rd_tag region_of _ _ _ Hg2) as (r & Hr & Ht & Erg).
  rewrite forallb_forall in Hall. pose proof (Hall r Hr) as Hrc. unfold region_side_chkX in Hrc.
  pose proof (i63_range pn) as Hpn0.
  destruct (shvis_chk r) eqn:Esv.
  { left. intros x Hx Hxl. apply (shvis_sound t rg r Hg Ht Erg HK Hz Esv).
    rewrite Erg in Hlo, Hxl. cbn [region_of rg_lo rg_len] in Hlo, Hxl. lia. }
  destruct (xa_pages_chk r) eqn:Exa.
  { unfold xa_pages_chk in Exa. destruct (rd_dflt r) as [kd|] eqn:Ed; [discriminate|].
    apply andb_prop in Exa as [Ht0 Exa]. apply negb_true_iff in Ht0. rewrite Ht in Ht0.
    unfold page_at in Hp. rewrite Erg in Hp. cbn [region_of rg_pages rg_dflt] in Hp.
    destruct (iget pn (iof_list (map (fun p0 => (pd_pn p0, page_of p0)) (rd_pages r)))) as [p1|] eqn:Hex.
    2:{ rewrite Ht0, Ed in Hp. discriminate. }
    destruct (iget_iof_list_map_In pd_pn page_of _ _ _ Hex) as (pd & Hpd & Epn & _). subst pn.
    rewrite forallb_forall in Exa. pose proof (Exa pd Hpd) as Hpc.
    destruct (xa_page_in r pd) eqn:Exi.
    2:{ (* [comment removed for export] *)
      left. apply andb_prop in Hpc as [Hpc Hv]. apply andb_prop in Hpc as [_ Hfull]. apply Z.leb_le in Hfull.
      pose proof (vis_root_sound segs E TT kn H FULL M0 HTT sx_noseg (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) (xt_of TT) eq_refl sx_M0) as visb_nh.
      intros x Hx _. rewrite <- Ht. apply (visb_nh _ _ _ Hv). lia. }
    right. right. clear Hpc. unfold xa_page_in in Exi.
    apply existsb_exists in Exi as ([[te o] l] & He & Hec). apply andb_prop in Hec as [Hec E2]. apply andb_prop in Hec as [Ete E1].
    apply Uint63.eqb_spec in Ete. subst te. apply Z.leb_le in E1, E2. rewrite Ht in *.
    intros x Hx. destruct Hrok as (_ & _ & Hb63 & _).
    pose proof (br_u64 (rho t)) as Hu. pose proof (i63_range o) as Ho. pose proof (i63_range l) as Hl.
    assert (Hlt' : to_Z (pd_pn pd) * 4096 + 4096 <= to_Z o + to_Z l) by exact E2.
    unfold xain. apply existsb_exists. exists (t, o, l). split; [exact He|].
    assert (Hrl : to_Z (pd_pn pd) * 4096 < to_Z (rg_len rg)) by exact Hlt.
    rewrite (adr_unsigned rho t (to_Z (pd_pn pd) * 4096 + x)) by lia.
    apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  unfold region_side_chk in Hrc. cbn [region_of rg_lo rg_len] in *.
  rewrite Erg in Hlo, Hlt. cbn [region_of rg_lo rg_len] in Hlo, Hlt.
  assert (Elen : to_Z (rg_len rg) = to_Z (rd_len r)) by (rewrite Erg; reflexivity).
  pose proof (i63_range (rd_lo r)) as Hl0.
  pose proof (vis_root_sound segs E TT kn H FULL M0 HTT sx_noseg (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) (xt_of TT) eq_refl sx_M0) as visb_nh.
  rewrite <- Ht in *.
  destruct (rd_tag r =? 0)%uint63 eqn:Et.
  - left. intros x Hx Hxl. rewrite Elen in Hxl. apply Uint63.eqb_spec in Et. rewrite Et.
    apply andb_prop in Hrc as [H1 H2]. apply Z.leb_le in H1, H2.
    unfold adr. rewrite (rho_of_0 TT E).
    replace (bv_add (Z_to_bv 64 0) (Z_to_bv 64 (to_Z pn * 4096 + x))) with (Z_to_bv 64 (to_Z pn * 4096 + x)).
    + apply sx_hull. lia.
    + apply bv_eq. rewrite bv_add_unsigned. change (bv_unsigned (Z_to_bv 64 0)) with 0.
      rewrite Z.add_0_l, bv_wrap_small by apply bv_unsigned_in_range. reflexivity.
  - destruct (rd_dflt r) as [kd|] eqn:Ed.
    + left. intros x Hx Hxl. rewrite Elen in Hxl.
      replace (to_Z pn * 4096 + x) with (to_Z (rd_lo r) + (to_Z pn * 4096 + x - to_Z (rd_lo r))) by lia.
      apply (visb_nh _ _ _ Hrc). lia.
    + unfold page_at in Hp. rewrite Erg in Hp. cbn [region_of rg_pages rg_dflt] in Hp.
      destruct (iget pn (iof_list (map (fun p0 => (pd_pn p0, page_of p0)) (rd_pages r)))) as [p1|] eqn:Hex.
      * injection Hp as <-.
        destruct (iget_iof_list_map_In pd_pn page_of _ _ _ Hex) as (pd & Hpd & Epn & ->). subst pn.
        rewrite forallb_forall in Hrc. pose proof (Hrc pd Hpd) as Hpc. unfold page_side_chk in Hpc.
        cbn [page_of pg_wr]. destruct (pd_wr pd) eqn:Ew.
        -- left. intros x Hx Hxl. rewrite Elen in Hxl. apply (visb_nh _ _ _ Hpc). unfold page_ext. lia.
        -- right. left. split; [reflexivity|]. apply andb_prop in Hpc as [Hal Hwit]. apply Z.leb_le in Hal.
           destruct Hrok as (_ & _ & _ & _ & Hmod & _). rewrite Erg in Hmod. cbn [region_of rg_align] in Hmod.
           split.
           { pose proof (i63_range (rd_align r)) as Ha0.
             assert (Hdiv : (4096 | 2 ^ to_Z (rd_align r))).
             { exists (2 ^ (to_Z (rd_align r) - 12)). change 4096 with (2 ^ 12). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
             apply Z.mod_divide; [lia|]. apply (Z.divide_trans _ _ _ Hdiv).
             apply Z.mod_divide; [apply Z.pow_nonzero; lia | exact Hmod]. }
           apply existsb_exists in Hwit as (c & _ & Hc). apply andb_prop in Hc as [Hc512 Hv]. apply Z.ltb_lt in Hc512.
           pose proof (i63_range (fst c)) as Hc0.
           exists (to_Z (fst c) * 8). split; [lia|].
           replace (to_Z (pd_pn pd) * 4096 + to_Z (fst c) * 8) with (to_Z (pd_pn pd) * 4096 + to_Z (fst c) * 8 + 0) by lia.
           apply (visb_nh _ _ _ Hv). lia.
      * rewrite Et, Ed in Hp. discriminate.
Qed.

Theorem side_cwX : side_chkX = true ->
  forall x, claimed_wr IM rho M0 x -> H x = false \/ xain rho XA (bv_unsigned x) = true.
Proof.
  intros Hside x (t & rg & pn & p & j & Hg & Hpn & Hp & Hwr & Hj & Hjl & ->).
  destruct (page_classX t rg pn p Hside Hg Hpn Hp) as [Hnh | [(Hro & _) | Hxa]];
    [left; exact (Hnh j Hj Hjl) | congruence | right; exact (Hxa j Hj)].
Qed.

Theorem side_LZX : side_chkX = true ->
  LZ IM rho (m_vm_lazy m) (map (denA rho) XA ++ CXS.allowA A E CS) M0.
Proof.
  intros Hside t rg pn p x Hg Hpn Hp Hx Hxl Hlz.
  pose proof (CXS.lazy_cover_cs segs A Lim (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None)
                HULL_ok SINV argH ISP FS0 0%nat E CS R FULL m HCS) as Hcover.
  destruct (sx_M0 t rg Hg) as (_ & _ & Hb63 & _).
  pose proof (br_u64 (rho t)) as Hu. pose proof (i63_range pn) as Hpn0.
  destruct (proj1 Hmem0 t rg Hg) as [_ Hpages0]. destruct (Hpages0 pn p Hpn Hp) as (_ & _ & Hlt0 & _).
  assert (Hadr : forall y, 0 <= y < 4096 ->
            bv_unsigned (adr rho t (to_Z pn * 4096 + y)) = bv_unsigned (rho t) + to_Z pn * 4096 + y).
  { intros y Hy. rewrite adr_unsigned by lia. lia. }
  destruct (page_classX t rg pn p Hside Hg Hpn Hp) as [Hnh | [(_ & Hmod & y & Hy & Hnhy) | Hxa]].
  - apply page_allowedb_app_r.
    pose proof (Hcover (adr rho t (to_Z pn * 4096 + x))) as Hc. unfold page_base in Hc.
    rewrite (Hadr x Hx) in Hc. exact (Hc Hlz (Hnh x Hx Hxl)).
  - apply page_allowedb_app_r.
    pose proof (Hcover (adr rho t (to_Z pn * 4096 + y))) as Hc. unfold page_base in Hc.
    rewrite (Hadr y Hy) in Hc.
    assert (Epg : page_base_of (bv_unsigned (rho t) + to_Z pn * 4096 + y)
                  = page_base_of (bv_unsigned (rho t) + to_Z pn * 4096 + x)).
    { unfold page_base_of, page_size. f_equal. clear - Hmod Hx Hy. Z.div_mod_to_equations. lia. }
    rewrite Epg in Hc. exact (Hc Hlz Hnhy).
  - (* [comment removed for export] *)
    pose proof (Hxa x Hx) as Hin. rewrite (Hadr x Hx) in Hin. unfold xain in Hin.
    apply existsb_exists in Hin as ([[te o] l] & He & Hec). apply andb_prop in Hec as [Z1 Z2]. apply Z.leb_le in Z1. apply Z.ltb_lt in Z2.
    unfold LazyCfg.page_allowedb. apply existsb_exists. exists (denA rho (te, o, l)). split.
    + apply in_or_app. left. apply in_map. exact He.
    + set (z := bv_unsigned (rho t) + to_Z pn * 4096 + x) in *.
      pose proof (br_u64 (rho te)) as Hue. pose proof (i63_range o) as Ho. pose proof (i63_range l) as Hl.
      assert (Ez : bv_unsigned (page_base_of z) = z / 4096 * 4096).
      { unfold page_base_of, page_size. apply br_lit_small. assert (Hz63 : 0 <= z < 2 ^ 63) by (unfold z; lia). clear - Hz63. Z.div_mod_to_equations. lia. }
      unfold denA. cbn [fst snd]. unfold pg_dn, pg_upZ. rewrite Ez. unfold page_size.
      apply andb_true_iff. split; apply Z.leb_le; clear - Z1 Z2; Z.div_mod_to_equations; lia.
Qed.

End SideX.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition w64_eqb (a b : w64) : bool := (wtop a =? wtop b)%uint63 && (wlo a =? wlo b)%uint63.
Lemma w64_eqb_eq a b : w64_eqb a b = true -> a = b.
Proof.
  destruct a as [at_ al], b as [bt bl]. unfold w64_eqb. cbn [wtop wlo]. intros H. apply andb_prop in H as [H1 H2].
  apply Uint63.eqb_spec in H1, H2. subst. reflexivity.
Qed.

Definition hfact_eqb (f g : hfact) : bool :=
  match f, g with
  | HCell t o n w, HCell t' o' n' w' => (t =? t')%uint63 && (o =? o')%uint63 && (n =? n')%uint63 && w64_eqb w w'
  | HVal t o v, HVal t' o' v' => (t =? t')%uint63 && (o =? o')%uint63 && fval_eqb v v'
  | HBytes t o n v, HBytes t' o' n' v' => (t =? t')%uint63 && (o =? o')%uint63 && (n =? n')%uint63 && fval_eqb v v'
  | HZero t o l, HZero t' o' l' => (t =? t')%uint63 && (o =? o')%uint63 && (l =? l')%uint63
  | HClear a b, HClear a' b' => (a =? a')%uint63 && (b =? b')%uint63
  | HWr t o l, HWr t' o' l' => (t =? t')%uint63 && (o =? o')%uint63 && (l =? l')%uint63
  | HReg r v, HReg r' v' => (r =? r')%uint63 && fval_eqb v v'
  | HRegion t a b c, HRegion t' a' b' c' => (t =? t')%uint63 && (a =? a')%uint63 && (b =? b')%uint63 && (c =? c')%uint63
  | HDisj t a b u c e, HDisj t' a' b' u' c' e' =>
      (t =? t')%uint63 && (a =? a')%uint63 && (b =? b')%uint63 && (u =? u')%uint63 && (c =? c')%uint63 && (e =? e')%uint63
  | _, _ => false
  end.

Lemma hfact_eqb_eq f g : hfact_eqb f g = true -> f = g.
Proof.
  destruct f, g; cbn [hfact_eqb]; try discriminate; intros H;
    repeat match goal with
           | H : (_ && _)%bool = true |- _ => apply andb_prop in H as [H ?]
           end;
    repeat match goal with
           | H : (_ =? _)%uint63 = true |- _ => apply Uint63.eqb_spec in H
           | H : fval_eqb _ _ = true |- _ => apply fval_eqb_eq in H
           | H : w64_eqb _ _ = true |- _ => apply w64_eqb_eq in H
           end; subst; reflexivity.
Qed.

Definition facts_sub (FL ALLF : list hfact) : bool := forallb (fun f => existsb (hfact_eqb f) ALLF) FL.

Lemma facts_sub_in FL ALLF : facts_sub FL ALLF = true -> forall f, In f FL -> In f ALLF.
Proof.
  unfold facts_sub. intros H f Hf. rewrite forallb_forall in H. pose proof (H f Hf) as He.
  apply existsb_exists in He as (g & Hg & Eq). apply hfact_eqb_eq in Eq. subst g. exact Hg.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition disj_chkR (ra : ra_t) (TT : ttab_e) (c1 c2 : list Z) (t1 lo1 len1 t2 lo2 len2 : int) : bool :=
  chain_apart (fun x y =>
    chain_apart (fun x2 y2 => ra (tte TT t1) x (y - x) (tte TT t2) x2 (y2 - x2)) (to_Z lo2) c2 (to_Z len2))
    (to_Z lo1) c1 (to_Z len1).
Definition rb_dfactR (ra : ra_t) (TT : ttab_e) (cuts : list (int * list Z)) (classes : list (int * rclass)) (r r' : rshape) : list hfact :=
  if (sh_tag r =? sh_tag r')%uint63 then []
  else if cls_neq classes r r' then [HDisj (sh_tag r) (sh_lo r) (sh_len r) (sh_tag r') (sh_lo r') (sh_len r')]
  else if disj_chkR ra TT (cuts_of cuts (sh_tag r)) (cuts_of cuts (sh_tag r')) (sh_tag r) (sh_lo r) (sh_len r) (sh_tag r') (sh_lo r') (sh_len r')
       then [HDisj (sh_tag r) (sh_lo r) (sh_len r) (sh_tag r') (sh_lo r') (sh_len r')] else [].
Fixpoint rb_pairsR (ra : ra_t) (TT : ttab_e) (cuts : list (int * list Z)) (classes : list (int * rclass)) (l : list rshape) : list hfact :=
  match l with
  | [] => []
  | r :: rest => flat_map (rb_dfactR ra TT cuts classes r) rest ++ rb_pairsR ra TT cuts classes rest
  end.
Definition rb_factsR (ra : ra_t) A TT shapes cuts classes CS : list hfact :=
  rb_rfacts shapes ++ rb_pairsR ra TT cuts classes shapes ++ rb_gfacts TT CS ++ rb_kfacts A TT shapes CS.
Lemma rb_pairsR_eq TT cuts classes CS : forall l, rb_pairsR (AX2.ranges_apart (CAP.kn CS)) TT cuts classes l = rb_pairs TT cuts classes CS l.
Proof. induction l as [|r rest IH]; [reflexivity|]. cbn [rb_pairsR rb_pairs]. rewrite IH. reflexivity. Qed.
Lemma rb_factsR_eq ra A TT shapes cuts classes CS : ra = AX2.ranges_apart (CAP.kn CS) ->
  rb_factsR ra A TT shapes cuts classes CS = rb_facts A TT shapes cuts classes CS.
Proof. intros ->. unfold rb_factsR, rb_facts. rewrite rb_pairsR_eq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TransX.
Variable cfg : SpuriousCfg.
Variable segs : list Segment.
Variable IM : fimage.
Variable code : itrie finstr.
Hypothesis Hcode : code_ok segs code.
Hypothesis Halloc : sc_alloc cfg = false.
Hypothesis HIM : image_ok segs IM.
Hypothesis HWR : image_wr_ok IM.
Variable A : CAP.atable.
Variable Lim : Z.
Variable SINV : AX2.env -> (word -> option byte) -> Prop.
Variable argH : AX2.env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis SEGS_in_hull : forall a : word, CXS.in_hull A (bv_unsigned a) = false -> find_segment segs (bv_unsigned a) 1 = None.
Hypothesis HULL_ok : CXS.hull_ok A.
Hypothesis argH_high : forall E (a : word), argH E a = true -> CAP.CEIL <= bv_unsigned a /\ ISP <= bv_unsigned a.
Variable nx0 : nat.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 CAP.e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), AxSymRun3.env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, AxSymRun3.env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.

Variable TT : ttab_e.
Variable n : int.
Variable shapes : list rshape.
Variable cuts : list (int * list Z).
Variable classes : list (int * rclass).
Variable CS : CAP.acs.
Variable d : sdesc.
Variable bs : list ditem.
Variable L3 : fledger3.
Variable W : Z.
Variables Rb Rc : Z.
Variable shp : int -> bool.
Variable xask : fstate -> option (int * int).
Variable bp : int.
Variable k fuel : nat.
Variable END : CAP.acs.
Variable aux : fstate -> fledger3 -> int -> LeafAux.
Variable XF : list hfact.            (* [comment removed for export] *)
Variable XA : list fent.             (* [comment removed for export] *)
(* [comment removed for export] *)
Variable hk : hooksel.               (* [comment removed for export] *)

(* [comment removed for export] *)
Definition skel : sdesc := SD (sd_pc d) (sd_regs d) [].

Definition rootx_chk : bool :=
  (CAP.no_fog (CAP.a_maps CS) && CxOpt.ledger_pos (CAP.kn CS) (CAP.a_maps CS))     (* [comment removed for export] *)
  && (let RF := rb_factsR (ra_fast (CAP.kn CS)) A TT shapes cuts classes CS in   (* [comment removed for export] *)
      let FC := rb_fillcov TT shapes CS in                    (* [comment removed for export] *)
      rb_check_with IM A TT n shapes classes CS RF skel
      && (xf_all A CS TT RF FC bs XF && ho_check2L IM (XF ++ RF) d))    (* [comment removed for export] *)
  && forallb (fact_tags_lt n) XF.

Lemma rootx_Rn E R FULL m :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m -> Forall (ditem_ok (rho_of TT E)) bs -> rootx_chk = true ->
  tt_wf TT = true
  /\ Rn segs IM n (rho_of TT E) (state_of d) (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)).
Proof.
  intros HCS Hdok Hc. unfold rootx_chk in Hc. cbv zeta in Hc.
  rewrite (rb_factsR_eq _ A TT shapes cuts classes CS (ra_fast_eq (CAP.kn CS))) in Hc.
  apply andb_prop in Hc as [Hc Hxlt]. apply andb_prop in Hc as [Hnf Hc]. apply andb_prop in Hc as [Hrb0 Hx].
  apply andb_prop in Hnf as [Hnf Hpos].
  pose proof (CxOpt.ledger_exact_intro segs E _ (CAP.kn CS) (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) _ Hnf Hpos) as Hlx.     (* [comment removed for export] *)
  change (rb_check IM A TT n shapes cuts classes CS skel = true) in Hrb0.
  apply andb_prop in Hx as [Hxf Hho]. apply ho_check2L_ok in Hho. apply xf_all_ok in Hxf.
  pose proof (rb_parts IM A TT n shapes cuts classes CS skel Hrb0) as (HTT & _ & _ & Hlt & Hpc).
  pose proof (rb_facts_hold segs IM A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high TT n shapes cuts classes CS skel
                E R FULL m HCS Hrb0) as HRF.
  split; [exact HTT|].
  assert (HALLF : Forall (hholds segs (rho_of TT E) (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)))
                         (XF ++ rb_facts A TT shapes cuts classes CS)).
  { apply Forall_app. split; [|exact HRF]. rewrite forallb_forall in Hxf. apply Forall_forall. intros f Hf.
    exact (xf_chk_sound segs A Lim SINV argH ISP FS0 E CS R FULL m HCS Hlx TT _ HRF _
             (rb_fillcov_hold segs IM A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high TT n shapes cuts classes CS skel E R FULL m HCS Hrb0)
             bs Hdok f (Hxf f Hf)). }
  apply (handoff_Rn2 segs IM HIM HWR (XF ++ rb_facts A TT shapes cuts classes CS) d n).
  - exact Hho.
  - rewrite forallb_app, Hlt, Hxlt. reflexivity.
  - exact (rho_of_0 TT E).
  - exact HALLF.
  - cbn [ms_pc_val PropExec.mkst]. rewrite Hpc. reflexivity.
  - reflexivity.
  - reflexivity.
Qed.

Definition trans3x_chk : bool :=
  rootx_chk
  && forallb (dress_chkL TT (CAP.kn CS) n (fl_ord L3)) bs
  && side_chkXP A CS TT d bs XA
  && rest3x_chk segs IM code A Lim nx0 TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux XA hk.

Theorem fx_transform3x E R FULL m T :
  CXS.cs_ok segs A Lim SINV argH ISP FS0 E CS R FULL m ->
  trans3x_chk = true -> (k <= 61)%nat ->
  (forall E1 R1 FULL1 m1,
     AxSymRun3.env_agree (CAP.nxt CS) E E1 ->
     CXS.cs_ok segs A Lim SINV argH ISP FS0 E1 END R1 FULL1 m1 ->
     m_fs m1 = m_fs m ->
     realizes_cfg cfg segs (CXS.cfg_of segs R1 (AX2.s_pc (CAP.a_ss END)) FULL1 m1) T) ->
  realizes_cfg cfg segs (CXS.cfg_of segs R (AX2.s_pc (CAP.a_ss CS)) FULL m) T.
Proof.
  intros HCS Hchk Hk HK. unfold trans3x_chk in Hchk.
  apply andb_prop in Hchk as [Hc Hrest]. apply andb_prop in Hc as [Hc Hside]. apply side_chkXP_ok in Hside. apply andb_prop in Hc as [Hrx Hdress].
  destruct (dress_chkL_all segs E TT (CAP.kn CS) _ (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) n (fl_ord L3) bs Hdress) as [Hdlt Hdok].
  destruct (rootx_Rn E R FULL m HCS Hdok Hrx) as [HTT HRn0].
  assert (Hlx : CxOpt.ledger_exact E (CAP.a_maps CS)).     (* [comment removed for export] *)
  { unfold rootx_chk in Hrx. do 2 (apply andb_prop in Hrx as [Hrx _]). apply andb_prop in Hrx as [Hnf0 Hpos0].
    exact (CxOpt.ledger_exact_intro segs E _ (CAP.kn CS) (CXS.co_know _ _ _ _ _ _ _ _ _ _ _ _ HCS) _ Hnf0 Hpos0). }
  pose proof (CxOpt.ledger_exact_nf _ _ Hlx) as Hnf.
  assert (HR0 : FxRel.R segs IM (rho_of TT E) (state_of d) (PropExec.mkst R (Z_to_bv 64 (AX2.s_pc (CAP.a_ss CS))) FULL (PropExec.seg_rom segs)))
    by (apply HRn0; split; [exact (rho_of_0 TT E) | intros; reflexivity]).
  pose proof (R_mem _ _ _ _ _ HR0) as Hmem0. cbn [ms_mem PropExec.mkst] in Hmem0.
  apply (fx_transform3_genX cfg segs IM code Hcode Halloc HIM HWR A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high nx0 NX0_spw
           argH_agree SINV_agree SINV_frame TT n classes CS d bs L3 W Rb Rc shp xask bp k fuel END aux XA hk
           E R FULL m T HCS HTT HRn0 Hdlt Hdok); [ | | exact Hrest | exact Hk | exact HK].
  - exact (side_LZX segs IM A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E CS R FULL m HCS Hlx TT HTT d bs XA Hdok Hmem0 Hside).
  - exact (side_cwX segs IM A Lim SINV argH ISP FS0 SEGS_in_hull HULL_ok argH_high E CS R FULL m HCS Hlx TT HTT d bs XA Hdok Hmem0 Hside).
Qed.

Theorem fx_hole3x_chk :
  trans3x_chk = true -> (k <= 61)%nat ->
  fx_hole cfg segs A Lim SINV argH ISP FS0 CS END.
Proof.
  intros Hchk Hk E R FULL m T HCS HK. exact (fx_transform3x E R FULL m T HCS Hchk Hk HK).
Qed.

End TransX.
