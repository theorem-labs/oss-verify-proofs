(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLin FxCore FxSound FxMem FxFold FxRgs FxFacts FxImg FxStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxLoop.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxSubst FxEnt FxLoop FxPlan FxFrame.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxCall.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Inductive waction : Type :=
| WGen (g : sst -> plan)
| WCall (c : csite)
| WTmpl (P : sst) (p : plan)     (* [comment removed for export] *)
| WGenT (mk : list sst -> sst) (g : sst -> plan)   (* [comment removed for export] *)
| WHand (f : sst -> option sst)   (* [comment removed for export] *)
| WCallK (c : csite)              (* [comment removed for export] *)
| WFragK (c : csite) (pcQ : Z).   (* [comment removed for export] *)
Definition WPlan (p : plan) : waction := WGen (fun _ => p).

Section WCheck.
Variable t : tree xi.
Variable img : tree Z.
Variable ins : list positive.
Variable depth : nat.
Variable s0 : sst.        (* [comment removed for export] *)

Definition wjoin (Ls : list sst) : option sst :=
  match Ls with
  | [] => None
  | L0 :: Lrs =>
      let '(P, k) := gen2 L0 Lrs in
      let n := max_next Lrs (s_next L0) in
      if (state_wf P && forallb (fun L => (join_ent L P (match_st L P) n k && params_fixed (match_st L P) ins)%bool) (L0 :: Lrs)
          && shape_eqb (s_rgs s0) (s_rgs P) && Pos.leb (s_next s0) (s_next P))%bool then Some P else None
  end.

Definition wtmpl (P : sst) (Ls : list sst) : bool :=
  (state_wf P && forallb (fun L => (entails L P (match_st L P) && params_fixed (match_st L P) ins)%bool) Ls
   && shape_eqb (s_rgs s0) (s_rgs P) && Pos.leb (s_next s0) (s_next P))%bool.

Fixpoint wcalls (c : csite) (ls : list sst) : option (list sst) :=
  match ls with
  | [] => Some []
  | L :: ls' =>
      match call_cont L (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c L) (ret_of L), wcalls c ls' with
      | Some K, Some ks => Some (K :: ks)
      | _, _ => None
      end
  end.

Fixpoint whand (f : sst -> option sst) (ls : list sst) : option (list sst) :=
  match ls with
  | [] => Some []
  | L :: ls' => match f L, whand f ls' with Some K, Some ks => Some (K :: ks) | _, _ => None end
  end.

Fixpoint wfrags (c : csite) (pcQ : Z) (ls : list sst) : option (list sst) :=
  match ls with
  | [] => Some []
  | L :: ls' =>
      match frag_cont L (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c L) pcQ, wfrags c pcQ ls' with
      | Some K, Some ks => Some (K :: ks)
      | _, _ => None
      end
  end.

Fixpoint wcheck (nodes : list (Z * waction)) (pend : list sst) : option (list sst) :=
  match nodes with
  | [] => Some pend
  | (pc, a) :: rest =>
      let here := List.filter (fun L => Z.eqb (s_pc L) pc) pend in
      let others := List.filter (fun L => negb (Z.eqb (s_pc L) pc)) pend in
      match here with
      | [] => wcheck rest others
      | _ :: _ =>
          match a with
          | WGen g => match wjoin here with
                      | Some P => match check t img ins depth (g P) P with Some f => wcheck rest (others ++ f) | None => None end
                      | None => None
                      end
          | WCall c => match wcalls c here with Some ks => wcheck rest (others ++ ks) | None => None end
          | WTmpl P p => if wtmpl P here then
                           match check t img ins depth p P with Some f => wcheck rest (others ++ f) | None => None end
                         else None
          | WGenT mk g => let P := mk here in
                          if wtmpl P here then
                            match check t img ins depth (g P) P with Some f => wcheck rest (others ++ f) | None => None end
                          else None
          | WHand f => match whand f here with Some ks => wcheck rest (others ++ ks) | None => None end
          | WCallK c => match wcalls c here with Some ks => wcheck rest (others ++ ks) | None => None end
          | WFragK c pcQ => match wfrags c pcQ here with Some ks => wcheck rest (others ++ ks) | None => None end
          end
      end
  end.

(* [comment removed for export] *)
Definition wstart (p0 : plan) (nodes : list (Z * waction)) : option (list sst) :=
  match check t img ins depth p0 s0 with Some f => wcheck nodes f | None => None end.
End WCheck.

(* [comment removed for export] *)
Fixpoint wsites (nodes : list (Z * waction)) : list (sst * sst) :=
  match nodes with
  | [] => []
  | (_, WCall c) :: rest => (cs_p0 c, cs_q c) :: wsites rest
  | _ :: rest => wsites rest
  end.
(* [comment removed for export] *)
Fixpoint wksites (nodes : list (Z * waction)) : list (sst * sst) :=
  match nodes with
  | [] => []
  | (_, WCallK c) :: rest => (cs_p0 c, cs_q c) :: wksites rest
  | _ :: rest => wksites rest
  end.
(* [comment removed for export] *)
Fixpoint wfsites (nodes : list (Z * waction)) : list (sst * sst * Z) :=
  match nodes with
  | [] => []
  | (_, WFragK c pcQ) :: rest => (cs_p0 c, cs_q c, pcQ) :: wfsites rest
  | _ :: rest => wfsites rest
  end.
(* [comment removed for export] *)
Fixpoint whands (nodes : list (Z * waction)) : list (sst -> option sst) :=
  match nodes with
  | [] => []
  | (_, WHand f) :: rest => f :: whands rest
  | _ :: rest => whands rest
  end.

Section WSound.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition hand_ok (f : sst -> option sst) : Prop :=
  forall L K E ms, f L = Some K -> sden segs E L ms ->
    exists ms' E', isteps segs ms ms' /\ sden segs E' K ms' /\ agree (s_next L) E E' /\
      (forall x, fr_pt E (s_rgs L) x -> ms_mem ms' x = ms_mem ms x) /\
      shape (s_rgs K) = shape (s_rgs L) /\ (s_next L <= s_next K)%positive /\ rtm (s_rgs K) = rtm (s_rgs L).

#[using="Type"] Lemma whand_in : forall f ls ks L, whand f ls = Some ks -> In L ls -> exists K, f L = Some K /\ In K ks.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros f. induction ls as [|L0 ls IH]; intros ks L H HL; [destruct HL|]. cbn [whand] in H.
  destruct (f L0) as [K0|] eqn:H0; [|discriminate]. destruct (whand f ls) as [ks'|] eqn:H1; [|discriminate]. injection H as <-.
  destruct HL as [<-|HL]; [exists K0; split; [exact H0 | left; reflexivity]|].
  destruct (IH ks' L eq_refl HL) as (K & HK & Hin). exists K. split; [exact HK | right; exact Hin].
Qed.

(* [comment removed for export] *)
Definition winv (ins : list positive) (s0 : sst) (E0 : valu) (ms0 : machine_state) (L : sst) (ms : machine_state) (E : valu) : Prop :=
  isteps segs ms0 ms /\ sden segs E L ms /\ (forall x, In x ins -> E x = E0 x) /\
  (forall x, fr_pt E0 (s_rgs s0) x -> ms_mem ms x = ms_mem ms0 x) /\ shape (s_rgs L) = shape (s_rgs s0) /\
  (s_next s0 <= s_next L)%positive /\ rtm (s_rgs L) = rtm (s_rgs s0).

#[using="Type"] Lemma winv_fr : forall ins s0 E0 ms0 L ms E x, bases_ins ins (s_rgs s0) = true -> winv ins s0 E0 ms0 L ms E ->
  fr_pt E0 (s_rgs s0) x -> fr_pt E (s_rgs L) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ins s0 E0 ms0 L ms E x Hbi (_ & _ & Hi & _ & Hsh & _ & Hrt) Hx.
  apply (fr_pt_shape E (s_rgs s0) (s_rgs L) x Hsh Hrt). apply (proj1 (fr_pt_params E0 E ins (s_rgs s0) x Hbi Hi)). exact Hx.
Qed.

#[using="Type"] Lemma wjoin_sound : forall ins s0 E0 ms0 here P L ms E, bases_ins ins (s_rgs s0) = true ->
  wjoin ins s0 here = Some P -> In L here -> winv ins s0 E0 ms0 L ms E ->
  exists E', sden segs E' P ms /\ (forall x, In x ins -> E' x = E0 x) /\ (forall x, fr_pt E0 (s_rgs s0) x -> fr_pt E' (s_rgs P) x) /\
    shape (s_rgs P) = shape (s_rgs s0) /\ (s_next s0 <= s_next P)%positive /\ rtm (s_rgs P) = rtm (s_rgs s0) /\ state_wf P = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ins s0 E0 ms0 here P L ms E Hbi Hj HL Hinv.
  destruct here as [|L0 Lrs]; [discriminate|]. unfold wjoin in Hj.
  destruct (gen2 L0 Lrs) as [P' k] eqn:Hgen. set (n := max_next Lrs (s_next L0)) in *.
  destruct (state_wf P' && forallb (fun L => (join_ent L P' (match_st L P') n k && params_fixed (match_st L P') ins)%bool) (L0 :: Lrs)
            && shape_eqb (s_rgs s0) (s_rgs P') && Pos.leb (s_next s0) (s_next P'))%bool eqn:Hw; [|discriminate].
  injection Hj as <-.
  apply andb_prop in Hw as [Hw HnP]. apply andb_prop in Hw as [Hw HshP]. apply Pos.leb_le in HnP. apply shape_eqb_eq in HshP.
  apply andb_prop in Hw as [Hwf Hall]. rewrite forallb_forall in Hall.
  pose proof (Hall L HL) as HLe. apply andb_prop in HLe as [Hje Hfix].
  pose proof Hinv as (Hst & Hd & Hi & Hfr & Hsh & Hn & Hrt).
  pose proof (sden0_sden segs P' (ecomp E (match_st L P')) ms Hwf (join_ent_sound segs E L P' (match_st L P') n k ms (sden_0 _ _ _ _ Hd) Hje)) as HdP.
  assert (Hrg : rgs_ent (s_rgs L) (s_rgs P') (match_st L P') = true).
  { unfold join_ent in Hje. apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [Hje _].
    apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [_ Hrg]. exact Hrg. }
  exists (ecomp E (match_st L P')). split; [exact HdP|].
  split; [intros x Hx; rewrite (params_fixed_sound E _ ins x Hfix Hx); exact (Hi x Hx)|].
  split; [intros x Hx; apply (fr_pt_ent E (s_rgs L) (s_rgs P') (match_st L P') x Hrg); exact (winv_fr ins s0 E0 ms0 L ms E x Hbi Hinv Hx)|].
  split; [symmetry; exact HshP|]. split; [exact HnP|]. split; [|exact Hwf].
  rewrite <- (rgs_ent_rtm _ _ _ Hrg). exact Hrt.
Qed.

#[using="Type"] Lemma wtmpl_sound : forall ins s0 E0 ms0 here P L ms E, bases_ins ins (s_rgs s0) = true ->
  wtmpl ins s0 P here = true -> In L here -> winv ins s0 E0 ms0 L ms E ->
  exists E', sden segs E' P ms /\ (forall x, In x ins -> E' x = E0 x) /\ (forall x, fr_pt E0 (s_rgs s0) x -> fr_pt E' (s_rgs P) x) /\
    shape (s_rgs P) = shape (s_rgs s0) /\ (s_next s0 <= s_next P)%positive /\ rtm (s_rgs P) = rtm (s_rgs s0) /\ state_wf P = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ins s0 E0 ms0 here P L ms E Hbi Hw HL Hinv. unfold wtmpl in Hw.
  apply andb_prop in Hw as [Hw HnP]. apply andb_prop in Hw as [Hw HshP]. apply Pos.leb_le in HnP. apply shape_eqb_eq in HshP.
  apply andb_prop in Hw as [Hwf Hall]. rewrite forallb_forall in Hall.
  pose proof (Hall L HL) as HLe. apply andb_prop in HLe as [Hje Hfix].
  pose proof Hinv as (Hst & Hd & Hi & Hfr & Hsh & Hn & Hrt).
  pose proof (entails_sden segs E L P (match_st L P) ms (sden_0 _ _ _ _ Hd) Hje Hwf) as HdP.
  assert (Hrg : rgs_ent (s_rgs L) (s_rgs P) (match_st L P) = true).
  { unfold entails in Hje. apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [_ Hrg]. exact Hrg. }
  exists (ecomp E (match_st L P)). split; [exact HdP|].
  split; [intros x Hx; rewrite (params_fixed_sound E _ ins x Hfix Hx); exact (Hi x Hx)|].
  split; [intros x Hx; apply (fr_pt_ent E (s_rgs L) (s_rgs P) (match_st L P) x Hrg); exact (winv_fr ins s0 E0 ms0 L ms E x Hbi Hinv Hx)|].
  split; [symmetry; exact HshP|]. split; [exact HnP|]. split; [|exact Hwf].
  rewrite <- (rgs_ent_rtm _ _ _ Hrg). exact Hrt.
Qed.

#[using="Type"] Lemma wfrags_in : forall c pcQ ls ks L, wfrags c pcQ ls = Some ks -> In L ls ->
  exists K, frag_cont L (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c L) pcQ = Some K /\ In K ks.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c pcQ. induction ls as [|L0 ls IH]; intros ks L H HL; [destruct HL|]. cbn [wfrags] in H.
  destruct (frag_cont L0 (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c L0) pcQ) as [K0|] eqn:H0; [|discriminate].
  destruct (wfrags c pcQ ls) as [ks'|] eqn:H1; [|discriminate]. injection H as <-.
  destruct HL as [<-|HL]; [exists K0; split; [exact H0 | left; reflexivity]|].
  destruct (IH ks' L eq_refl HL) as (K & HK & Hin). exists K. split; [exact HK | right; exact Hin].
Qed.
#[using="Type"] Lemma wcalls_in : forall c ls ks L, wcalls c ls = Some ks -> In L ls ->
  exists K, call_cont L (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c L) (ret_of L) = Some K /\ In K ks.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c. induction ls as [|L0 ls IH]; intros ks L H HL; [destruct HL|]. cbn [wcalls] in H.
  destruct (call_cont L0 (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c L0) (ret_of L0)) as [K0|] eqn:H0; [|discriminate].
  destruct (wcalls c ls) as [ks'|] eqn:H1; [|discriminate]. injection H as <-.
  destruct HL as [<-|HL]; [exists K0; split; [exact H0 | left; reflexivity]|].
  destruct (IH ks' L eq_refl HL) as (K & HK & Hin). exists K. split; [exact HK | right; exact Hin].
Qed.

#[using="Type"] Theorem wcheck_sound : forall t img ins depth s0 nodes pend finals,
  tbl_ok segs t -> img_ok segs img -> wcheck t img ins depth s0 nodes pend = Some finals ->
  (forall P0 Q, In (P0, Q) (wsites nodes) -> exists rets, fn_ok segs P0 Q rets) ->
  (forall f, In f (whands nodes) -> hand_ok f) ->
  (forall P0 Q, In (P0, Q) (wksites nodes) -> kfn_ok segs P0 Q) ->
  (forall P0 Q pcQ, In (P0, Q, pcQ) (wfsites nodes) -> kfrag_ok segs P0 Q pcQ) ->
  bases_ins ins (s_rgs s0) = true -> forallb (fun x => Pos.ltb x (s_next s0)) ins = true ->
  forall E0 ms0, (exists L ms E, In L pend /\ winv ins s0 E0 ms0 L ms E) ->
  exists L ms E, In L finals /\ winv ins s0 E0 ms0 L ms E.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth s0 nodes. induction nodes as [|[pc a] rest IH]; intros pend finals Ht Himg Hc Hsites Hhand Hks Hfs Hbi Hib E0 ms0 (L & ms & E & HL & Hinv);
    cbn [wcheck] in Hc.
  - injection Hc as <-. exists L, ms, E. split; [exact HL | exact Hinv].
  - set (here := List.filter (fun L => Z.eqb (s_pc L) pc) pend) in *.
    set (others := List.filter (fun L => negb (Z.eqb (s_pc L) pc)) pend) in *.
    destruct (Z.eqb (s_pc L) pc) eqn:Hpc.
    + (* [comment removed for export] *)
      assert (Hh : In L here) by (apply filter_In; split; [exact HL | exact Hpc]).
      destruct here as [|L0 Lrs] eqn:Hhere; [destruct Hh|].
      destruct a as [g|c|P p|mk g|fh|c|c pcQ].
      * destruct (wjoin ins s0 (L0 :: Lrs)) as [P|] eqn:Hj; [|discriminate].
        destruct (check t img ins depth (g P) P) as [f|] eqn:Hck; [|discriminate].
        destruct (wjoin_sound ins s0 E0 ms0 (L0 :: Lrs) P L ms E Hbi Hj Hh Hinv) as (E' & HdP & HiP & HfrP & HshP & HnP & HrtP & HwP).
        assert (HbP : bases_ins ins (s_rgs P) = true) by (apply (bases_ins_shape ins (s_rgs s0)); [exact HshP | exact Hbi]).
        destruct (check_frame_fr segs t img ins depth (g P) P f Ht Himg Hck E' ms HdP (state_wf_bases _ HwP) HbP)
          as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfr2 & Hsh2 & Hn2 & Hrt2).
        apply (IH (others ++ f) finals Ht Himg Hc (fun P0 Q H => Hsites P0 Q H) (fun g' H => Hhand g' H) (fun P0 Q H => Hks P0 Q H) (fun P0 Q pcQ H => Hfs P0 Q pcQ H) Hbi Hib E0 ms0).
        exists L2, ms2, E2. split; [apply in_or_app; right; exact HL2|].
        pose proof Hinv as (Hst & _ & _ & Hfr & _ & _ & _).
        split; [eapply isteps_trans; [exact Hst | exact Hst2]|]. split; [exact Hd2|].
        split; [intros x Hx; rewrite (Hi2 x Hx); exact (HiP x Hx)|].
        split; [intros x Hx; rewrite (Hfr2 x (HfrP x Hx)); exact (Hfr x Hx)|].
        split; [rewrite Hsh2; exact HshP|]. split; [lia|]. rewrite Hrt2; exact HrtP.
      * destruct (wcalls c (L0 :: Lrs)) as [ks|] eqn:Hw; [|discriminate].
        destruct (wcalls_in c (L0 :: Lrs) ks L Hw Hh) as (K & HK & HinK).
        assert (Hs : In (cs_p0 c, cs_q c) (wsites ((pc, WCall c) :: rest))) by (left; reflexivity).
        destruct (Hsites _ _ Hs) as (rets & Hfn).
        pose proof Hinv as (Hst & Hd & Hi & Hfr & Hsh & Hn & Hrt).
        destruct (call_sound segs _ _ rets _ _ _ _ _ L K E ms Hfn HK Hd) as (ms2 & E2 & Hst2 & Hd2 & Ha2 & Hfr2).
        destruct (call_cont_shape _ _ _ _ _ _ _ _ _ HK) as (HshK & HnK & HrtK).
        apply (IH (others ++ ks) finals Ht Himg Hc (fun P0 Q H => Hsites P0 Q (or_intror H)) (fun g' H => Hhand g' H) (fun P0 Q H => Hks P0 Q H) (fun P0 Q pcQ H => Hfs P0 Q pcQ H) Hbi Hib E0 ms0).
        exists K, ms2, E2. split; [apply in_or_app; right; exact HinK|].
        split; [eapply isteps_trans; [exact Hst | exact Hst2]|]. split; [exact Hd2|].
        rewrite forallb_forall in Hib.
        split; [intros x Hx; rewrite <- (Ha2 x ltac:(pose proof (Hib x Hx) as X; apply Pos.ltb_lt in X; lia)); exact (Hi x Hx)|].
        split; [intros x Hx; rewrite (Hfr2 x (winv_fr ins s0 E0 ms0 L ms E x Hbi Hinv Hx)); exact (Hfr x Hx)|].
        split; [rewrite HshK; exact Hsh|]. split; [lia|]. rewrite HrtK; exact Hrt.
      * destruct (wtmpl ins s0 P (L0 :: Lrs)) eqn:Hj; [|discriminate].
        destruct (check t img ins depth p P) as [f|] eqn:Hck; [|discriminate].
        destruct (wtmpl_sound ins s0 E0 ms0 (L0 :: Lrs) P L ms E Hbi Hj Hh Hinv) as (E' & HdP & HiP & HfrP & HshP & HnP & HrtP & HwP).
        assert (HbP : bases_ins ins (s_rgs P) = true) by (apply (bases_ins_shape ins (s_rgs s0)); [exact HshP | exact Hbi]).
        destruct (check_frame_fr segs t img ins depth p P f Ht Himg Hck E' ms HdP (state_wf_bases _ HwP) HbP)
          as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfr2 & Hsh2 & Hn2 & Hrt2).
        apply (IH (others ++ f) finals Ht Himg Hc (fun P0 Q H => Hsites P0 Q H) (fun g' H => Hhand g' H) (fun P0 Q H => Hks P0 Q H) (fun P0 Q pcQ H => Hfs P0 Q pcQ H) Hbi Hib E0 ms0).
        exists L2, ms2, E2. split; [apply in_or_app; right; exact HL2|].
        pose proof Hinv as (Hst & _ & _ & Hfr & _ & _ & _).
        split; [eapply isteps_trans; [exact Hst | exact Hst2]|]. split; [exact Hd2|].
        split; [intros x Hx; rewrite (Hi2 x Hx); exact (HiP x Hx)|].
        split; [intros x Hx; rewrite (Hfr2 x (HfrP x Hx)); exact (Hfr x Hx)|].
        split; [rewrite Hsh2; exact HshP|]. split; [lia|]. rewrite Hrt2; exact HrtP.
      * set (P := mk (L0 :: Lrs)) in *.
        destruct (wtmpl ins s0 P (L0 :: Lrs)) eqn:Hj; [|discriminate].
        destruct (check t img ins depth (g P) P) as [f|] eqn:Hck; [|discriminate].
        destruct (wtmpl_sound ins s0 E0 ms0 (L0 :: Lrs) P L ms E Hbi Hj Hh Hinv) as (E' & HdP & HiP & HfrP & HshP & HnP & HrtP & HwP).
        assert (HbP : bases_ins ins (s_rgs P) = true) by (apply (bases_ins_shape ins (s_rgs s0)); [exact HshP | exact Hbi]).
        destruct (check_frame_fr segs t img ins depth (g P) P f Ht Himg Hck E' ms HdP (state_wf_bases _ HwP) HbP)
          as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfr2 & Hsh2 & Hn2 & Hrt2).
        apply (IH (others ++ f) finals Ht Himg Hc (fun P0 Q H => Hsites P0 Q H) (fun g' H => Hhand g' H) (fun P0 Q H => Hks P0 Q H) (fun P0 Q pcQ H => Hfs P0 Q pcQ H) Hbi Hib E0 ms0).
        exists L2, ms2, E2. split; [apply in_or_app; right; exact HL2|].
        pose proof Hinv as (Hst & _ & _ & Hfr & _ & _ & _).
        split; [eapply isteps_trans; [exact Hst | exact Hst2]|]. split; [exact Hd2|].
        split; [intros x Hx; rewrite (Hi2 x Hx); exact (HiP x Hx)|].
        split; [intros x Hx; rewrite (Hfr2 x (HfrP x Hx)); exact (Hfr x Hx)|].
        split; [rewrite Hsh2; exact HshP|]. split; [lia|]. rewrite Hrt2; exact HrtP.
      * (* [comment removed for export] *)
        destruct (whand fh (L0 :: Lrs)) as [ks|] eqn:Hw; [|discriminate].
        destruct (whand_in fh (L0 :: Lrs) ks L Hw Hh) as (K & HK & HinK).
        assert (Hok : hand_ok fh) by (apply Hhand; left; reflexivity).
        pose proof Hinv as (Hst & Hd & Hi & Hfr & Hsh & Hn & Hrt).
        destruct (Hok L K E ms HK Hd) as (ms2 & E2 & Hst2 & Hd2 & Ha2 & Hfr2 & HshK & HnK & HrtK).
        apply (IH (others ++ ks) finals Ht Himg Hc (fun P0 Q H => Hsites P0 Q H) (fun g' H => Hhand g' (or_intror H)) (fun P0 Q H => Hks P0 Q H) (fun P0 Q pcQ H => Hfs P0 Q pcQ H) Hbi Hib E0 ms0).
        exists K, ms2, E2. split; [apply in_or_app; right; exact HinK|].
        split; [eapply isteps_trans; [exact Hst | exact Hst2]|]. split; [exact Hd2|].
        rewrite forallb_forall in Hib.
        split; [intros x Hx; rewrite <- (Ha2 x ltac:(pose proof (Hib x Hx) as X; apply Pos.ltb_lt in X; lia)); exact (Hi x Hx)|].
        split; [intros x Hx; rewrite (Hfr2 x (winv_fr ins s0 E0 ms0 L ms E x Hbi Hinv Hx)); exact (Hfr x Hx)|].
        split; [rewrite HshK; exact Hsh|]. split; [lia|]. rewrite HrtK; exact Hrt.
      * (* [comment removed for export] *)
        destruct (wcalls c (L0 :: Lrs)) as [ks|] eqn:Hw; [|discriminate].
        destruct (wcalls_in c (L0 :: Lrs) ks L Hw Hh) as (K & HK & HinK).
        assert (Hs : In (cs_p0 c, cs_q c) (wksites ((pc, WCallK c) :: rest))) by (left; reflexivity).
        pose proof (Hks _ _ Hs) as Hfn.
        pose proof Hinv as (Hst & Hd & Hi & Hfr & Hsh & Hn & Hrt).
        destruct (call_sound_k segs _ _ _ _ _ _ _ L K E ms Hfn HK Hd) as (ms2 & E2 & Hst2 & Hd2 & Ha2 & Hfr2).
        destruct (call_cont_shape _ _ _ _ _ _ _ _ _ HK) as (HshK & HnK & HrtK).
        apply (IH (others ++ ks) finals Ht Himg Hc (fun P0 Q H => Hsites P0 Q H) (fun g' H => Hhand g' H) (fun P0 Q H => Hks P0 Q (or_intror H)) (fun P0 Q pcQ H => Hfs P0 Q pcQ H) Hbi Hib E0 ms0).
        exists K, ms2, E2. split; [apply in_or_app; right; exact HinK|].
        split; [eapply isteps_trans; [exact Hst | exact Hst2]|]. split; [exact Hd2|].
        rewrite forallb_forall in Hib.
        split; [intros x Hx; rewrite <- (Ha2 x ltac:(pose proof (Hib x Hx) as X; apply Pos.ltb_lt in X; lia)); exact (Hi x Hx)|].
        split; [intros x Hx; rewrite (Hfr2 x (winv_fr ins s0 E0 ms0 L ms E x Hbi Hinv Hx)); exact (Hfr x Hx)|].
        split; [rewrite HshK; exact Hsh|]. split; [lia|]. rewrite HrtK; exact Hrt.
      * (* [comment removed for export] *)
        destruct (wfrags c pcQ (L0 :: Lrs)) as [ks|] eqn:Hw; [|discriminate].
        destruct (wfrags_in c pcQ (L0 :: Lrs) ks L Hw Hh) as (K & HK & HinK).
        assert (Hs : In (cs_p0 c, cs_q c, pcQ) (wfsites ((pc, WFragK c pcQ) :: rest))) by (left; reflexivity).
        pose proof (Hfs _ _ _ Hs) as Hfn.
        pose proof Hinv as (Hst & Hd & Hi & Hfr & Hsh & Hn & Hrt).
        destruct (frag_sound_k segs _ _ _ _ _ _ _ L K E ms Hfn HK Hd) as (ms2 & E2 & Hst2 & Hd2 & Ha2 & Hfr2).
        destruct (frag_cont_shape _ _ _ _ _ _ _ _ _ HK) as (HshK & HnK & HrtK).
        apply (IH (others ++ ks) finals Ht Himg Hc (fun P0 Q H => Hsites P0 Q H) (fun g' H => Hhand g' H) (fun P0 Q H => Hks P0 Q H) (fun P0 Q pcQ' H => Hfs P0 Q pcQ' (or_intror H)) Hbi Hib E0 ms0).
        exists K, ms2, E2. split; [apply in_or_app; right; exact HinK|].
        split; [eapply isteps_trans; [exact Hst | exact Hst2]|]. split; [exact Hd2|].
        rewrite forallb_forall in Hib.
        split; [intros x Hx; rewrite <- (Ha2 x ltac:(pose proof (Hib x Hx) as X; apply Pos.ltb_lt in X; lia)); exact (Hi x Hx)|].
        split; [intros x Hx; rewrite (Hfr2 x (winv_fr ins s0 E0 ms0 L ms E x Hbi Hinv Hx)); exact (Hfr x Hx)|].
        split; [rewrite HshK; exact Hsh|]. split; [lia|]. rewrite HrtK; exact Hrt.
    + (* [comment removed for export] *)
      assert (Ho : In L others) by (apply filter_In; split; [exact HL | rewrite Hpc; reflexivity]).
      assert (Hs' : forall P0 Q, In (P0, Q) (wsites rest) -> exists rets, fn_ok segs P0 Q rets).
      { intros P0 Q H. apply Hsites. destruct a; [exact H | right; exact H | exact H | exact H | exact H | exact H | exact H]. }
      assert (Hh' : forall f, In f (whands rest) -> hand_ok f).
      { intros f H. apply Hhand. destruct a; [exact H | exact H | exact H | exact H | right; exact H | exact H | exact H]. }
      assert (Hk' : forall P0 Q, In (P0, Q) (wksites rest) -> kfn_ok segs P0 Q).
      { intros P0 Q H. apply Hks. destruct a; [exact H | exact H | exact H | exact H | exact H | right; exact H | exact H]. }
      assert (Hf' : forall P0 Q pcQ, In (P0, Q, pcQ) (wfsites rest) -> kfrag_ok segs P0 Q pcQ).
      { intros P0 Q pcQ H. apply Hfs. destruct a; [exact H | exact H | exact H | exact H | exact H | exact H | right; exact H]. }
      destruct here as [|L0 Lrs] eqn:Hhere.
      * exact (IH others finals Ht Himg Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0 (ex_intro _ L (ex_intro _ ms (ex_intro _ E (conj Ho Hinv))))).
      * destruct a as [g|c|P p|mk g|fh|c|c pcQ].
        -- destruct (wjoin ins s0 (L0 :: Lrs)) as [P|]; [|discriminate].
           destruct (check t img ins depth (g P) P) as [f|]; [|discriminate].
           apply (IH (others ++ f) finals Ht Himg Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists L, ms, E. split; [apply in_or_app; left; exact Ho | exact Hinv].
        -- destruct (wcalls c (L0 :: Lrs)) as [ks|]; [|discriminate].
           apply (IH (others ++ ks) finals Ht Himg Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists L, ms, E. split; [apply in_or_app; left; exact Ho | exact Hinv].
        -- destruct (wtmpl ins s0 P (L0 :: Lrs)); [|discriminate].
           destruct (check t img ins depth p P) as [f|]; [|discriminate].
           apply (IH (others ++ f) finals Ht Himg Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists L, ms, E. split; [apply in_or_app; left; exact Ho | exact Hinv].
        -- destruct (wtmpl ins s0 (mk (L0 :: Lrs)) (L0 :: Lrs)); [|discriminate].
           destruct (check t img ins depth (g (mk (L0 :: Lrs))) (mk (L0 :: Lrs))) as [f|]; [|discriminate].
           apply (IH (others ++ f) finals Ht Himg Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists L, ms, E. split; [apply in_or_app; left; exact Ho | exact Hinv].
        -- destruct (whand fh (L0 :: Lrs)) as [ks|]; [|discriminate].
           apply (IH (others ++ ks) finals Ht Himg Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists L, ms, E. split; [apply in_or_app; left; exact Ho | exact Hinv].
        -- destruct (wcalls c (L0 :: Lrs)) as [ks|]; [|discriminate].
           apply (IH (others ++ ks) finals Ht Himg Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists L, ms, E. split; [apply in_or_app; left; exact Ho | exact Hinv].
        -- destruct (wfrags c pcQ (L0 :: Lrs)) as [ks|]; [|discriminate].
           apply (IH (others ++ ks) finals Ht Himg Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists L, ms, E. split; [apply in_or_app; left; exact Ho | exact Hinv].
Qed.

#[using="Type"] Theorem wstart_sound : forall t img ins depth s0 p0 nodes finals,
  tbl_ok segs t -> img_ok segs img -> wstart t img ins depth s0 p0 nodes = Some finals ->
  (forall P0 Q, In (P0, Q) (wsites nodes) -> exists rets, fn_ok segs P0 Q rets) ->
  (forall f, In f (whands nodes) -> hand_ok f) ->
  (forall P0 Q, In (P0, Q) (wksites nodes) -> kfn_ok segs P0 Q) ->
  (forall P0 Q pcQ, In (P0, Q, pcQ) (wfsites nodes) -> kfrag_ok segs P0 Q pcQ) ->
  bases_wf (s_next s0) (s_rgs s0) = true -> bases_ins ins (s_rgs s0) = true -> forallb (fun x => Pos.ltb x (s_next s0)) ins = true ->
  forall E0 ms0, sden segs E0 s0 ms0 -> exists L ms E, In L finals /\ winv ins s0 E0 ms0 L ms E.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth s0 p0 nodes finals Ht Himg Hc Hsites Hhand Hks Hfs Hw Hbi Hib E0 ms0 Hd. unfold wstart in Hc.
  destruct (check t img ins depth p0 s0) as [f|] eqn:Hck; [|discriminate].
  apply (wcheck_sound t img ins depth s0 nodes f finals Ht Himg Hc Hsites Hhand Hks Hfs Hbi Hib E0 ms0).
  destruct (check_frame_fr segs t img ins depth p0 s0 f Ht Himg Hck E0 ms0 Hd Hw Hbi) as (L & ms & E & HL & Hst & Hd1 & Hi & Hfr & Hsh & Hn & Hrt).
  exists L, ms, E. split; [exact HL|]. split; [exact Hst|]. split; [exact Hd1|]. split; [exact Hi|]. split; [exact Hfr|].
  split; [exact Hsh | split; [exact Hn | exact Hrt]].
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem fn_ok_of_wcert : forall t img depth p0 nodes P0 Q rets,
  tbl_ok segs t -> img_ok segs img ->
  all_fin (fin_q Q rets (s_next P0)) (wstart t img (vars_below (s_next P0)) depth P0 p0 nodes) = true ->
  (forall P0' Q', In (P0', Q') (wsites nodes) -> exists rets', fn_ok segs P0' Q' rets') ->
  (forall f, In f (whands nodes) -> hand_ok f) ->
  (forall P0' Q', In (P0', Q') (wksites nodes) -> kfn_ok segs P0' Q') ->
  (forall P0' Q' pcQ, In (P0', Q', pcQ) (wfsites nodes) -> kfrag_ok segs P0' Q' pcQ) ->
  bases_wf (s_next P0) (s_rgs P0) = true -> bases_ins (vars_below (s_next P0)) (s_rgs P0) = true -> state_wf Q = true ->
  Forall (is_ret segs) rets -> fn_ok segs P0 Q rets.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img depth p0 nodes P0 Q rets Ht Himg Hc Hsites Hhand Hks Hfs Hw1 Hw2 HwQ Hrets E ms Hd.
  destruct (all_fin_sound _ _ Hc) as (finals & Hck & Hfin).
  assert (Hib : forallb (fun x => Pos.ltb x (s_next P0)) (vars_below (s_next P0)) = true).
  { apply forallb_forall. intros x Hx. apply Pos.ltb_lt. exact (vars_below_lt _ x Hx). }
  destruct (wstart_sound t img (vars_below (s_next P0)) depth P0 p0 nodes finals Ht Himg Hck Hsites Hhand Hks Hfs Hw1 Hw2 Hib E ms Hd)
    as (L & ms' & E1 & HL & Hst & Hd1 & Hins & Hfr & _ & _ & _).
  pose proof (Hfin L HL) as HfL. unfold fin_q in HfL.
  set (σ := mq L (with_pc Q (s_pc L))) in HfL.
  apply andb_prop in HfL as [HfL Hfix]. apply andb_prop in HfL as [HfL Hent]. apply andb_prop in HfL as [Hp Hr].
  apply existsb_exists in Hp as (p0' & Hp0 & Hpe). apply Z.eqb_eq in Hpe.
  exists ms', (ecomp E1 σ), (s_pc L). split; [exact Hst|]. split; [rewrite Hpe; exact Hp0|].
  split; [rewrite Forall_forall in Hrets; apply Hrets; rewrite Hpe; exact Hp0|].
  split; [apply (entails_sden segs E1 L (with_pc Q (s_pc L)) σ ms' (sden_0 _ _ _ _ Hd1) Hent); rewrite state_wf_with_pc; exact HwQ|].
  split; [|exact Hfr].
  intros x Hx. rewrite <- (fixed_below_agree E1 σ (s_next P0) Hfix x Hx). symmetry. apply Hins. apply in_vars_below. exact Hx.
Qed.
End WSound.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lin_delta (a b : lin) : option Z := if terms_eqb (l_t a) (l_t b) then Some (sgn64 (w64 (l_c a - l_c b))) else None.
(* [comment removed for export] *)
Definition common_delta (P : sst) (backs : list sst) (key : positive) : option Z :=
  match backs with
  | [] => None
  | B :: Bs => match lin_delta (rget (s_regs B) key) (rget (s_regs P) key) with
               | Some d => if forallb (fun B' => match lin_delta (rget (s_regs B') key) (rget (s_regs P) key) with
                                                 | Some d' => Z.eqb d d' | None => false end) Bs then Some d else None
               | None => None
               end
  end.
Definition rkeys : list positive := List.map Pos.of_succ_nat (seq 1 31).

(* [comment removed for export] *)
Definition ptr_loop (t : tree xi) (img : tree Z) (fuel : nat) (stops : list Z) (P : sst) : plan :=
  let backs := List.filter (fun L => Z.eqb (s_pc L) (s_pc P)) (fx_explore t img fuel (s_pc P :: stops) P []) in
  let n0 := max_next backs (s_next P) in
  let deltas := List.map (fun key => (key, common_delta P backs key)) rkeys in
  let same := List.filter (fun key => forallb (fun B => lin_eqb (rget (s_regs B) key) (rget (s_regs P) key)) backs) rkeys in
  let cand := List.flat_map (fun '(z, od) => match od with
                 | Some dz => if Z.ltb 0 dz then
                                List.flat_map (fun e => let r := irange (s_facts P) (lsub (rget (s_regs P) e) (rget (s_regs P) z)) in
                                                        if (Z.leb 0 (fst r) && Z.leb (snd r) (2 ^ 48) && negb (Pos.eqb e z))%bool
                                                        then [(z, dz, e, fst r, snd r)] else []) same
                              else []
                 | None => [] end) deltas in
  (* [comment removed for export] *)
  let cmp := fun '(z, _, e, _, _) => forallb (fun B => let zv := rget (s_regs B) z in let ev := rget (s_regs B) e in
               existsb (fun f => match f with
                                 | FCond _ a b _ => ((lin_eqb a zv && lin_eqb b ev) || (lin_eqb a ev && lin_eqb b zv))%bool
                                 | _ => false end) (s_facts B)) backs in
  let cand1 := List.filter (fun '(_, dz, _, _, hi) => Z.leb dz hi) cand in
  let cand2 := match List.filter cmp cand1 with [] => cand1 | l => l end in
  (* [comment removed for export] *)
  let cand' := List.fold_left (fun acc c => match acc with
                                            | [] => [c]
                                            | (_, _, _, _, h0) :: _ => let '(_, _, _, _, h) := c in if Z.ltb h0 h then [c] else acc
                                            end) cand2 [] in
  match backs, cand' with
  | [], _ => PRun fuel stops []
  | _, [] => PLoopW fuel stops []
  | _, (z, dz, e, lo, hi) :: _ =>
      let X := lvar (n0 + z) in let z0 := rget (s_regs P) z in let Ev := rget (s_regs P) e in
      let regs := List.fold_left (fun acc '(key, od) =>
                    let v := rget (s_regs P) key in
                    rset acc key (if existsb (Pos.eqb key) same then v
                                  else if Pos.eqb key z then X
                                  else match od with
                                       | Some d => if Z.eqb (Z.rem d dz) 0 then ladd v (lscale (Z.quot d dz) (lsub X z0)) else lvar (n0 + key)
                                       | None => lvar (n0 + key)
                                       end)) deltas TEmpty in
      let base := match l_t z0 with
                  | [] => []
                  | tz => let c0 := sgn64 (l_c z0) in if Z.leb 0 c0 then [FRange (lsub X (LIN 0 tz)) c0 (2 ^ 48)] else []
                  end in
      let inv := SST (s_pc P) regs (gen_rgs (s_rgs P) (List.map s_rgs backs)) (FRange (lsub Ev X) lo hi :: base ++ s_facts P) (n0 + 33)
                     (if forallb (fun B => rsv_eqb (s_resv B) (s_resv P)) backs then s_resv P else RUnk) in
      PLoop (LS inv (lsub Ev X) (pos_upto (Pos.to_nat (s_next P) - 1) []) fuel stops) []
  end.
