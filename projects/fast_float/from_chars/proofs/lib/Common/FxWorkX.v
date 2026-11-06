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
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require FxDrv FxCall FxWork.
Import OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLin OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSound OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxMem OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFold OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxRgs OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFacts OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxImg OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxStep OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop.FxExplore OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxSubst OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxEnt OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxLoop OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxPlan OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxFrame OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv.FxGrow OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxDrv OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxCall OSSVerify.Proofs.fast_float.from_chars.lib.Common.FxWork.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Record xfact : Type := XF { xf_tag : nat ; xf_args : list lin }.
Definition xsubst (σ : tree lin) (f : xfact) : xfact := XF (xf_tag f) (List.map (lsubst σ) (xf_args f)).
Fixpoint lins_eqb (a b : list lin) : bool :=
  match a, b with
  | [], [] => true
  | x :: a', y :: b' => (lin_eqb x y && lins_eqb a' b')%bool
  | _, _ => false
  end.
Definition xf_eqb (f g : xfact) : bool := (Nat.eqb (xf_tag f) (xf_tag g) && lins_eqb (xf_args f) (xf_args g))%bool.
Definition xwf (n : positive) (f : xfact) : bool := forallb (lwf n) (xf_args f).

Lemma lins_eqb_eq : forall a b, lins_eqb a b = true -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; cbn [lins_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H2]. apply lin_eqb_eq in H1. rewrite H1, (IH b H2). reflexivity.
Qed.
Lemma xf_eqb_eq : forall f g, xf_eqb f g = true -> f = g.
Proof.
  intros [t a] [t' a'] H. unfold xf_eqb in H. cbn [xf_tag xf_args] in H. apply andb_prop in H as [H1 H2].
  apply Nat.eqb_eq in H1. rewrite H1, (lins_eqb_eq _ _ H2). reflexivity.
Qed.

(* [comment removed for export] *)
Record xst : Type := XST { xs_st : sst ; xs_x : list xfact }.

Inductive xaction : Type :=
| XGenTs (mk : list xst -> list (sst * list xfact) * list nat) (g : sst -> plan)
    (* [comment removed for export] *)
| XCall (c : csite)                 (* [comment removed for export] *)
| XCallK (c : csite)                (* [comment removed for export] *)
| XCallKs (cs : list csite)         (* [comment removed for export] *)
| XFragK (c : csite) (pcQ : Z)      (* [comment removed for export] *)
| XFragKs (cs : list csite) (pcQ : Z)   (* [comment removed for export] *)
| XHand (f : xst -> option (list xst)).   (* [comment removed for export] *)
Definition XGenT (mk : list sst -> sst) (xmk : list xst -> list xfact) (g : sst -> plan) : xaction :=
  XGenTs (fun l => ([(mk (List.map xs_st l), xmk l)], List.repeat 0%nat (List.length l))) g.

Section WCheckX.
Variable t : tree xi.
Variable img : tree Z.
Variable ins : list positive.
Variable depth : nat.
Variable s0 : sst.

Definition xent (P : sst) (XP : list xfact) (X : xst) : bool :=
  let L := xs_st X in let σ := match_st L P in
  (entails L P σ && params_fixed σ ins && forallb (fun f => existsb (xf_eqb (xsubst σ f)) (xs_x X)) XP)%bool.
Definition xtmpl_ok (P : sst) (XP : list xfact) : bool :=
  (state_wf P && shape_eqb (s_rgs s0) (s_rgs P) && Pos.leb (s_next s0) (s_next P) && forallb (xwf (s_next P)) XP)%bool.

(* [comment removed for export] *)
Fixpoint ent_ix (Ps : list (sst * list xfact)) (here : list xst) (ix : list nat) : bool :=
  match here, ix with
  | [], _ => true
  | X :: here', i :: ix' => match nth_error Ps i with Some (P, XP) => (xent P XP X && ent_ix Ps here' ix')%bool | None => false end
  | _ :: _, [] => false
  end.
Fixpoint xchecks (g : sst -> plan) (Ps : list (sst * list xfact)) : option (list xst) :=
  match Ps with
  | [] => Some []
  | (P, XP) :: Ps' =>
      if xtmpl_ok P XP then
        match check t img (vars_below (s_next P)) depth (g P) P, xchecks g Ps' with
        | Some f, Some r => Some (List.map (fun K => XST K XP) f ++ r)
        | _, _ => None
        end
      else None
  end.

Fixpoint xcalls (c : csite) (ls : list xst) : option (list xst) :=
  match ls with
  | [] => Some []
  | X :: ls' =>
      match call_cont (xs_st X) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X)) (ret_of (xs_st X)), xcalls c ls' with
      | Some K, Some ks => Some (XST K (xs_x X) :: ks)
      | _, _ => None
      end
  end.
Fixpoint xcall1 (cs : list csite) (X : xst) : option xst :=
  match cs with
  | [] => None
  | c :: cs' => match call_cont (xs_st X) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X)) (ret_of (xs_st X)) with
                | Some K => Some (XST K (xs_x X))
                | None => xcall1 cs' X
                end
  end.
Fixpoint xcallsm (cs : list csite) (ls : list xst) : option (list xst) :=
  match ls with
  | [] => Some []
  | X :: ls' => match xcall1 cs X, xcallsm cs ls' with Some K, Some ks => Some (K :: ks) | _, _ => None end
  end.
Fixpoint xfrags (c : csite) (pcQ : Z) (ls : list xst) : option (list xst) :=
  match ls with
  | [] => Some []
  | X :: ls' =>
      match frag_cont (xs_st X) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X)) pcQ, xfrags c pcQ ls' with
      | Some K, Some ks => Some (XST K (xs_x X) :: ks)
      | _, _ => None
      end
  end.
Fixpoint xfrag1 (cs : list csite) (pcQ : Z) (X : xst) : option xst :=
  match cs with
  | [] => None
  | c :: cs' => match frag_cont (xs_st X) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X)) pcQ with
                | Some K => Some (XST K (xs_x X))
                | None => xfrag1 cs' pcQ X
                end
  end.
Fixpoint xfragsm (cs : list csite) (pcQ : Z) (ls : list xst) : option (list xst) :=
  match ls with
  | [] => Some []
  | X :: ls' => match xfrag1 cs pcQ X, xfragsm cs pcQ ls' with Some K, Some ks => Some (K :: ks) | _, _ => None end
  end.
Fixpoint xhands (f : xst -> option (list xst)) (ls : list xst) : option (list xst) :=
  match ls with
  | [] => Some []
  | X :: ls' => match f X, xhands f ls' with Some ks, Some r => Some (ks ++ r) | _, _ => None end
  end.

Fixpoint wcheckx (nodes : list (Z * xaction)) (pend : list xst) : option (list xst) :=
  match nodes with
  | [] => Some pend
  | (pc, a) :: rest =>
      let here := List.filter (fun X => Z.eqb (s_pc (xs_st X)) pc) pend in
      let others := List.filter (fun X => negb (Z.eqb (s_pc (xs_st X)) pc)) pend in
      match here with
      | [] => wcheckx rest others
      | _ :: _ =>
          match a with
          | XGenTs mk g =>
              let '(Ps, ix) := mk here in
              if ent_ix Ps here ix then
                match xchecks g Ps with Some f => wcheckx rest (others ++ f) | None => None end
              else None
          | XCall c => match xcalls c here with Some ks => wcheckx rest (others ++ ks) | None => None end
          | XCallK c => match xcalls c here with Some ks => wcheckx rest (others ++ ks) | None => None end
          | XCallKs cs => match xcallsm cs here with Some ks => wcheckx rest (others ++ ks) | None => None end
          | XFragK c pcQ => match xfrags c pcQ here with Some ks => wcheckx rest (others ++ ks) | None => None end
          | XFragKs cs pcQ => match xfragsm cs pcQ here with Some ks => wcheckx rest (others ++ ks) | None => None end
          | XHand f => match xhands f here with Some ks => wcheckx rest (others ++ ks) | None => None end
          end
      end
  end.

(* [comment removed for export] *)
Definition wstartx (p0 : plan) (nodes : list (Z * xaction)) : option (list xst) :=
  match check t img ins depth p0 s0 with Some f => wcheckx nodes (List.map (fun K => XST K []) f) | None => None end.
End WCheckX.

Fixpoint xsites (nodes : list (Z * xaction)) : list (sst * sst) :=
  match nodes with [] => [] | (_, XCall c) :: rest => (cs_p0 c, cs_q c) :: xsites rest | _ :: rest => xsites rest end.
Fixpoint xksites (nodes : list (Z * xaction)) : list (sst * sst) :=
  match nodes with
  | [] => []
  | (_, XCallK c) :: rest => (cs_p0 c, cs_q c) :: xksites rest
  | (_, XCallKs cs) :: rest => List.map (fun c => (cs_p0 c, cs_q c)) cs ++ xksites rest
  | _ :: rest => xksites rest
  end.
Fixpoint xfsites (nodes : list (Z * xaction)) : list (sst * sst * Z) :=
  match nodes with
  | [] => []
  | (_, XFragK c pcQ) :: rest => (cs_p0 c, cs_q c, pcQ) :: xfsites rest
  | (_, XFragKs cs pcQ) :: rest => List.map (fun c => (cs_p0 c, cs_q c, pcQ)) cs ++ xfsites rest
  | _ :: rest => xfsites rest
  end.
Fixpoint xhandl (nodes : list (Z * xaction)) : list (xst -> option (list xst)) :=
  match nodes with [] => [] | (_, XHand f) :: rest => f :: xhandl rest | _ :: rest => xhandl rest end.

Section WSoundX.
Variable segs : list Segment.
Variable xok : nat -> list word -> (word -> option byte) -> Prop.

Definition xfact_ok (E : valu) (m0 : word -> option byte) (f : xfact) : Prop := xok (xf_tag f) (List.map (lden E) (xf_args f)) m0.

#[using="Type"] Lemma xfact_ok_subst : forall E σ m0 f, xfact_ok E m0 (xsubst σ f) -> xfact_ok (ecomp E σ) m0 f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros E σ m0 [tg a] H. unfold xfact_ok, xsubst in *. cbn [xf_tag xf_args] in *. rewrite List.map_map in H.
  replace (List.map (lden (ecomp E σ)) a) with (List.map (fun x => lden E (lsubst σ x)) a); [exact H|].
  apply List.map_ext. intros l. apply lden_lsubst.
Qed.
#[using="Type"] Lemma xfact_ok_agree : forall n E E' m0 f, xwf n f = true -> agree n E E' -> xfact_ok E m0 f -> xfact_ok E' m0 f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n E E' m0 [tg a] Hw Ha H. unfold xfact_ok, xwf in *. cbn [xf_tag xf_args] in *.
  replace (List.map (lden E') a) with (List.map (lden E) a); [exact H|].
  apply List.map_ext_in. intros l Hl. rewrite forallb_forall in Hw. exact (lden_agree n E E' l (Hw l Hl) Ha).
Qed.
#[using="Type"] Lemma xwf_mono : forall n n' fs, (n <= n')%positive -> forallb (xwf n) fs = true -> forallb (xwf n') fs = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros n n' fs Hn H. rewrite forallb_forall in *. intros f Hf. pose proof (H f Hf) as Hw. unfold xwf in *.
  rewrite forallb_forall in *. intros l Hl. exact (lwf_mono n n' l Hn (Hw l Hl)).
Qed.

(* [comment removed for export] *)
Definition hand_okx (f : xst -> option (list xst)) : Prop :=
  forall X Ks E ms (m0 : word -> option byte), f X = Some Ks -> sden segs E (xs_st X) ms ->
    Forall (xfact_ok E m0) (xs_x X) -> forallb (xwf (s_next (xs_st X))) (xs_x X) = true ->
    (forall x, fr_pt E (s_rgs (xs_st X)) x -> ms_mem ms x = m0 x) ->
    exists K ms' E', In K Ks /\ isteps segs ms ms' /\ sden segs E' (xs_st K) ms' /\ agree (s_next (xs_st X)) E E' /\
      (forall x, fr_pt E (s_rgs (xs_st X)) x -> ms_mem ms' x = ms_mem ms x) /\
      shape (s_rgs (xs_st K)) = shape (s_rgs (xs_st X)) /\ (s_next (xs_st X) <= s_next (xs_st K))%positive /\
      rtm (s_rgs (xs_st K)) = rtm (s_rgs (xs_st X)) /\
      Forall (xfact_ok E' m0) (xs_x K) /\ forallb (xwf (s_next (xs_st K))) (xs_x K) = true.

(* [comment removed for export] *)
Definition hand_okxP (Φ : machine_state -> machine_state -> Prop) (f : xst -> option (list xst)) : Prop :=
  forall X Ks E ms (m0 : word -> option byte), f X = Some Ks -> sden segs E (xs_st X) ms ->
    Forall (xfact_ok E m0) (xs_x X) -> forallb (xwf (s_next (xs_st X))) (xs_x X) = true ->
    (forall x, fr_pt E (s_rgs (xs_st X)) x -> ms_mem ms x = m0 x) ->
    exists K ms' E', In K Ks /\ isteps segs ms ms' /\ sden segs E' (xs_st K) ms' /\ agree (s_next (xs_st X)) E E' /\
      (forall x, fr_pt E (s_rgs (xs_st X)) x -> ms_mem ms' x = ms_mem ms x) /\
      shape (s_rgs (xs_st K)) = shape (s_rgs (xs_st X)) /\ (s_next (xs_st X) <= s_next (xs_st K))%positive /\
      rtm (s_rgs (xs_st K)) = rtm (s_rgs (xs_st X)) /\
      Forall (xfact_ok E' m0) (xs_x K) /\ forallb (xwf (s_next (xs_st K))) (xs_x K) = true /\ Φ ms ms'.
Definition hand_okx_fp (f : xst -> option (list xst)) : Prop := hand_okxP fpeq f.
#[using="Type"] Lemma hand_okx_P : forall f, hand_okx f -> hand_okxP (fun _ _ => True) f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros f H X Ks E ms m0 H1 H2 H3 H4 H5. destruct (H X Ks E ms m0 H1 H2 H3 H4 H5) as (K & ms' & E' & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10).
  exists K, ms', E'. exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 (conj A10 I)))))))))).
Qed.

#[using="Type"] Lemma hand_okxP_ok : forall Φ f, hand_okxP Φ f -> hand_okx f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ f H X Ks E ms m0 H1 H2 H3 H4 H5. destruct (H X Ks E ms m0 H1 H2 H3 H4 H5) as (K & ms' & E' & A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & _).
  exists K, ms', E'. exact (conj A1 (conj A2 (conj A3 (conj A4 (conj A5 (conj A6 (conj A7 (conj A8 (conj A9 A10))))))))).
Qed.

(* [comment removed for export] *)
Definition winvx (ins : list positive) (s0 : sst) (E0 : valu) (ms0 : machine_state) (X : xst) (ms : machine_state) (E : valu) : Prop :=
  winv segs ins s0 E0 ms0 (xs_st X) ms E /\ Forall (xfact_ok E (ms_mem ms0)) (xs_x X) /\ forallb (xwf (s_next (xs_st X))) (xs_x X) = true.

#[using="Type"] Lemma bases_ins_mono : forall ins ins' rgs, (forall y, In y ins -> In y ins') -> bases_ins ins rgs = true -> bases_ins ins' rgs = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ins ins' rgs Hsub H. unfold bases_ins in *. rewrite forallb_forall in *. intros R HR. pose proof (H R HR) as HR'.
  cbv beta in HR' |- *. rewrite forallb_forall in *. intros [y k] Hy. pose proof (HR' (y, k) Hy) as Hy'. cbv beta in Hy' |- *.
  apply existsb_exists in Hy' as (z & Hz & Hzy). apply Pos.eqb_eq in Hzy. subst z.
  apply existsb_exists. exists y. split; [exact (Hsub y Hz) | apply Pos.eqb_refl].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma winv_fr_back : forall ins s0 E0 ms0 L ms E x, bases_ins ins (s_rgs s0) = true -> winv segs ins s0 E0 ms0 L ms E ->
  fr_pt E (s_rgs L) x -> fr_pt E0 (s_rgs s0) x.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ins s0 E0 ms0 L ms E x Hbi (_ & _ & Hi & _ & Hsh & _ & Hrt) Hx.
  apply (proj2 (fr_pt_params E0 E ins (s_rgs s0) x Hbi Hi)).
  apply (fr_pt_shape E (s_rgs L) (s_rgs s0) x ltac:(symmetry; exact Hsh) ltac:(symmetry; exact Hrt)). exact Hx.
Qed.

#[using="Type"] Lemma xent_sound : forall ins s0 E0 ms0 P XP X ms E, bases_ins ins (s_rgs s0) = true ->
  xent ins P XP X = true -> xtmpl_ok s0 P XP = true -> winvx ins s0 E0 ms0 X ms E ->
  exists E', sden segs E' P ms /\ (forall x, In x ins -> E' x = E0 x) /\ (forall x, fr_pt E0 (s_rgs s0) x -> fr_pt E' (s_rgs P) x) /\
    shape (s_rgs P) = shape (s_rgs s0) /\ (s_next s0 <= s_next P)%positive /\ rtm (s_rgs P) = rtm (s_rgs s0) /\ state_wf P = true /\
    Forall (xfact_ok E' (ms_mem ms0)) XP.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ins s0 E0 ms0 P XP X ms E Hbi He Hok ((Hst & Hd & Hi & Hfr & Hsh & Hn & Hrt) & HxF & Hxw).
  unfold xent in He. set (σ := match_st (xs_st X) P) in *.
  apply andb_prop in He as [He Hxs]. apply andb_prop in He as [Hje Hfix].
  unfold xtmpl_ok in Hok. apply andb_prop in Hok as [Hok HxwP]. apply andb_prop in Hok as [Hok HnP]. apply andb_prop in Hok as [Hwf HshP].
  apply Pos.leb_le in HnP. apply shape_eqb_eq in HshP.
  pose proof (entails_sden segs E (xs_st X) P σ ms (sden_0 _ _ _ _ Hd) Hje Hwf) as HdP.
  assert (Hrg : rgs_ent (s_rgs (xs_st X)) (s_rgs P) σ = true).
  { unfold entails in Hje. apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [Hje _]. apply andb_prop in Hje as [_ Hrg]. exact Hrg. }
  exists (ecomp E σ). split; [exact HdP|].
  split; [intros x Hx; rewrite (params_fixed_sound E σ ins x Hfix Hx); exact (Hi x Hx)|].
  split; [intros x Hx; apply (fr_pt_ent E (s_rgs (xs_st X)) (s_rgs P) σ x Hrg);
          exact (winv_fr segs ins s0 E0 ms0 (xs_st X) ms E x Hbi (conj Hst (conj Hd (conj Hi (conj Hfr (conj Hsh (conj Hn Hrt)))))) Hx)|].
  split; [symmetry; exact HshP|]. split; [exact HnP|]. split; [rewrite <- (rgs_ent_rtm _ _ _ Hrg); exact Hrt|]. split; [exact Hwf|].
  rewrite Forall_forall. intros f Hf. rewrite forallb_forall in Hxs. pose proof (Hxs f Hf) as Hex.
  apply existsb_exists in Hex as (g & Hg & Heq). apply xf_eqb_eq in Heq. subst g.
  rewrite Forall_forall in HxF. apply xfact_ok_subst. exact (HxF _ Hg).
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma ent_ix_in : forall ins Ps here ix X, ent_ix ins Ps here ix = true -> In X here ->
  exists P XP, In (P, XP) Ps /\ xent ins P XP X = true.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ins Ps. induction here as [|X0 here IH]; intros ix X H HX; [destruct HX|].
  destruct ix as [|i ix]; cbn [ent_ix] in H; [discriminate|].
  destruct (nth_error Ps i) as [[P XP]|] eqn:Hn; [|discriminate]. apply andb_prop in H as [H1 H2].
  destruct HX as [<-|HX].
  - exists P, XP. split; [exact (nth_error_In _ _ Hn) | exact H1].
  - exact (IH ix X H2 HX).
Qed.
#[using="Type"] Lemma xchecks_all : forall t img depth s0 g Ps f P XP, xchecks t img depth s0 g Ps = Some f -> In (P, XP) Ps ->
  xtmpl_ok s0 P XP = true /\ exists fP, check t img (vars_below (s_next P)) depth (g P) P = Some fP /\
    forall K, In K fP -> In (XST K XP) f.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img depth s0 g. induction Ps as [|[P0 XP0] Ps IH]; intros f P XP H HP; [destruct HP|]. cbn [xchecks] in H.
  destruct (xtmpl_ok s0 P0 XP0) eqn:Hok; [|discriminate].
  destruct (check t img (vars_below (s_next P0)) depth (g P0) P0) as [fP|] eqn:Hck; [|discriminate].
  destruct (xchecks t img depth s0 g Ps) as [r|] eqn:Hr; [|discriminate]. injection H as <-.
  destruct HP as [HP|HP].
  - injection HP as <- <-. split; [exact Hok|]. exists fP. split; [exact Hck|]. intros K HK. apply in_or_app. left. apply in_map_iff. exists K. split; [reflexivity | exact HK].
  - destruct (IH r P XP eq_refl HP) as (HokP & fP' & HckP & Hin). split; [exact HokP|]. exists fP'. split; [exact HckP|].
    intros K HK. apply in_or_app. right. exact (Hin K HK).
Qed.
#[using="Type"] Lemma xcalls_in : forall c ls ks X, xcalls c ls = Some ks -> In X ls ->
  exists K, call_cont (xs_st X) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X)) (ret_of (xs_st X)) = Some K /\ In (XST K (xs_x X)) ks.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c. induction ls as [|X0 ls IH]; intros ks X H HX; [destruct HX|]. cbn [xcalls] in H.
  destruct (call_cont (xs_st X0) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X0)) (ret_of (xs_st X0))) as [K0|] eqn:H0; [|discriminate].
  destruct (xcalls c ls) as [ks'|] eqn:H1; [|discriminate]. injection H as <-.
  destruct HX as [<-|HX]; [exists K0; split; [exact H0 | left; reflexivity]|].
  destruct (IH ks' X eq_refl HX) as (K & HK & Hin). exists K. split; [exact HK | right; exact Hin].
Qed.
#[using="Type"] Lemma xcallsm_in : forall cs ls ks X, xcallsm cs ls = Some ks -> In X ls ->
  exists c K, In c cs /\ call_cont (xs_st X) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X)) (ret_of (xs_st X)) = Some K /\
    In (XST K (xs_x X)) ks.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros cs. induction ls as [|X0 ls IH]; intros ks X H HX; [destruct HX|]. cbn [xcallsm] in H.
  destruct (xcall1 cs X0) as [K0|] eqn:H0; [|discriminate].
  destruct (xcallsm cs ls) as [ks'|] eqn:H1; [|discriminate]. injection H as <-.
  destruct HX as [<-|HX].
  - clear IH H1. induction cs as [|c cs IHc]; cbn [xcall1] in H0; [discriminate|].
    destruct (call_cont (xs_st X0) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X0)) (ret_of (xs_st X0))) as [K|] eqn:HK.
    + injection H0 as <-. exists c, K. split; [left; reflexivity|]. split; [exact HK | left; reflexivity].
    + destruct (IHc H0) as (c' & K' & Hc' & HK' & Hin'). exists c', K'. split; [right; exact Hc'|]. split; [exact HK' | exact Hin'].
  - destruct (IH ks' X eq_refl HX) as (c & K & Hc & HK & Hin). exists c, K. split; [exact Hc|]. split; [exact HK | right; exact Hin].
Qed.
#[using="Type"] Lemma xfrags_in : forall c pcQ ls ks X, xfrags c pcQ ls = Some ks -> In X ls ->
  exists K, frag_cont (xs_st X) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X)) pcQ = Some K /\ In (XST K (xs_x X)) ks.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros c pcQ. induction ls as [|X0 ls IH]; intros ks X H HX; [destruct HX|]. cbn [xfrags] in H.
  destruct (frag_cont (xs_st X0) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X0)) pcQ) as [K0|] eqn:H0; [|discriminate].
  destruct (xfrags c pcQ ls) as [ks'|] eqn:H1; [|discriminate]. injection H as <-.
  destruct HX as [<-|HX]; [exists K0; split; [exact H0 | left; reflexivity]|].
  destruct (IH ks' X eq_refl HX) as (K & HK & Hin). exists K. split; [exact HK | right; exact Hin].
Qed.
#[using="Type"] Lemma xfragsm_in : forall cs pcQ ls ks X, xfragsm cs pcQ ls = Some ks -> In X ls ->
  exists c K, In c cs /\ frag_cont (xs_st X) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X)) pcQ = Some K /\
    In (XST K (xs_x X)) ks.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros cs pcQ. induction ls as [|X0 ls IH]; intros ks X H HX; [destruct HX|]. cbn [xfragsm] in H.
  destruct (xfrag1 cs pcQ X0) as [K0|] eqn:H0; [|discriminate].
  destruct (xfragsm cs pcQ ls) as [ks'|] eqn:H1; [|discriminate]. injection H as <-.
  destruct HX as [<-|HX].
  - clear IH H1. induction cs as [|c cs IHc]; cbn [xfrag1] in H0; [discriminate|].
    destruct (frag_cont (xs_st X0) (cs_p0 c) (cs_q c) (cs_keep c) (cs_qk c) (cs_vs c) (cs_w c (xs_st X0)) pcQ) as [K|] eqn:HK.
    + injection H0 as <-. exists c, K. split; [left; reflexivity|]. split; [exact HK | left; reflexivity].
    + destruct (IHc H0) as (c' & K' & Hc' & HK' & Hin'). exists c', K'. split; [right; exact Hc'|]. split; [exact HK' | exact Hin'].
  - destruct (IH ks' X eq_refl HX) as (c & K & Hc & HK & Hin). exists c, K. split; [exact Hc|]. split; [exact HK | right; exact Hin].
Qed.
#[using="Type"] Lemma xhands_in : forall f ls ks X, xhands f ls = Some ks -> In X ls -> exists Ks, f X = Some Ks /\ forall K, In K Ks -> In K ks.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros f. induction ls as [|X0 ls IH]; intros ks X H HX; [destruct HX|]. cbn [xhands] in H.
  destruct (f X0) as [K0|] eqn:H0; [|discriminate]. destruct (xhands f ls) as [ks'|] eqn:H1; [|discriminate]. injection H as <-.
  destruct HX as [<-|HX]; [exists K0; split; [exact H0 | intros K HK; apply in_or_app; left; exact HK]|].
  destruct (IH ks' X eq_refl HX) as (Ks & HK & Hin). exists Ks. split; [exact HK | intros K HK'; apply in_or_app; right; exact (Hin K HK')].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma winvx_call : forall ins s0 E0 ms0 X K ms E ms2 E2, bases_ins ins (s_rgs s0) = true ->
  forallb (fun x => Pos.ltb x (s_next s0)) ins = true -> winvx ins s0 E0 ms0 X ms E ->
  isteps segs ms ms2 -> sden segs E2 K ms2 -> agree (s_next (xs_st X)) E E2 ->
  (forall x, fr_pt E (s_rgs (xs_st X)) x -> ms_mem ms2 x = ms_mem ms x) ->
  shape (s_rgs K) = shape (s_rgs (xs_st X)) -> (s_next (xs_st X) < s_next K)%positive -> rtm (s_rgs K) = rtm (s_rgs (xs_st X)) ->
  winvx ins s0 E0 ms0 (XST K (xs_x X)) ms2 E2.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros ins s0 E0 ms0 X K ms E ms2 E2 Hbi Hib (Hinv & HxF & Hxw) Hst2 Hd2 Ha2 Hfr2 HshK HnK HrtK.
  pose proof Hinv as (Hst & Hd & Hi & Hfr & Hsh & Hn & Hrt).
  split; [|split].
  - cbn [xs_st]. split; [eapply isteps_trans; [exact Hst | exact Hst2]|]. split; [exact Hd2|].
    rewrite forallb_forall in Hib.
    split; [intros x Hx; rewrite <- (Ha2 x ltac:(pose proof (Hib x Hx) as Y; apply Pos.ltb_lt in Y; lia)); exact (Hi x Hx)|].
    split; [intros x Hx; rewrite (Hfr2 x (winv_fr segs ins s0 E0 ms0 (xs_st X) ms E x Hbi Hinv Hx)); exact (Hfr x Hx)|].
    split; [rewrite HshK; exact Hsh|]. split; [lia|]. rewrite HrtK; exact Hrt.
  - cbn [xs_x]. rewrite Forall_forall in *. intros f Hf. rewrite forallb_forall in Hxw.
    exact (xfact_ok_agree _ E E2 _ f (Hxw f Hf) Ha2 (HxF f Hf)).
  - cbn [xs_x xs_st]. apply (xwf_mono (s_next (xs_st X))); [lia | exact Hxw].
Qed.

#[using="Type"] Theorem wcheckx_soundP : forall (Φ : machine_state -> machine_state -> Prop), fp_inv Φ -> (forall a b c, Φ a b -> Φ b c -> Φ a c) ->
  forall t img ins depth s0 nodes pend finals,
  tbl_ok segs t -> img_ok segs img -> (forall a b, fpc t a b -> Φ a b) -> wcheckx t img ins depth s0 nodes pend = Some finals ->
  (forall P0 Q, In (P0, Q) (xsites nodes) -> exists rets, fn_okP segs Φ P0 Q rets) ->
  (forall f, In f (xhandl nodes) -> hand_okxP Φ f) ->
  (forall P0 Q, In (P0, Q) (xksites nodes) -> kfn_okP segs Φ P0 Q) ->
  (forall P0 Q pcQ, In (P0, Q, pcQ) (xfsites nodes) -> kfrag_okP segs Φ P0 Q pcQ) ->
  bases_ins ins (s_rgs s0) = true -> forallb (fun x => Pos.ltb x (s_next s0)) ins = true ->
  forall E0 ms0, (exists X ms E, In X pend /\ winvx ins s0 E0 ms0 X ms E /\ Φ ms0 ms) ->
  exists X ms E, In X finals /\ winvx ins s0 E0 ms0 X ms E /\ Φ ms0 ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ HΦi HΦt t img ins depth s0 nodes. induction nodes as [|[pc a] rest IH]; intros pend finals Ht Himg HΦfx Hc Hsites Hhand Hks Hfs Hbi Hib E0 ms0 (X & ms & E & HX & Hinv & HΦ);
    cbn [wcheckx] in Hc.
  - injection Hc as <-. exists X, ms, E. split; [exact HX | split; [exact Hinv | exact HΦ]].
  - set (here := List.filter (fun X => Z.eqb (s_pc (xs_st X)) pc) pend) in *.
    set (others := List.filter (fun X => negb (Z.eqb (s_pc (xs_st X)) pc)) pend) in *.
    assert (Hs' : forall P0 Q, In (P0, Q) (xsites rest) -> exists rets, fn_okP segs Φ P0 Q rets).
    { intros P0 Q H. apply Hsites. destruct a; [exact H | right; exact H | exact H | exact H | exact H | exact H | exact H]. }
    assert (Hh' : forall f, In f (xhandl rest) -> hand_okxP Φ f).
    { intros f H. apply Hhand. destruct a; [exact H | exact H | exact H | exact H | exact H | exact H | right; exact H]. }
    assert (Hk' : forall P0 Q, In (P0, Q) (xksites rest) -> kfn_okP segs Φ P0 Q).
    { intros P0 Q H. apply Hks. destruct a; [exact H | exact H | right; exact H | cbn [xksites]; apply in_or_app; right; exact H | exact H | exact H | exact H]. }
    assert (Hf' : forall P0 Q pcQ, In (P0, Q, pcQ) (xfsites rest) -> kfrag_okP segs Φ P0 Q pcQ).
    { intros P0 Q pcQ H. apply Hfs. destruct a; [exact H | exact H | exact H | exact H | right; exact H | cbn [xfsites]; apply in_or_app; right; exact H | exact H]. }
    destruct (Z.eqb (s_pc (xs_st X)) pc) eqn:Hpc.
    + (* [comment removed for export] *)
      assert (Hh : In X here) by (apply filter_In; split; [exact HX | exact Hpc]).
      destruct here as [|X0 Xrs] eqn:Hhere; [destruct Hh|].
      destruct a as [mk g|c|c|cs|c pcQ|cs pcQ|fh].
      * destruct (mk (X0 :: Xrs)) as [Ps ix] eqn:Hmk.
        destruct (ent_ix ins Ps (X0 :: Xrs) ix) eqn:Hall; [|discriminate].
        destruct (xchecks t img depth s0 g Ps) as [f|] eqn:Hck; [|discriminate].
        destruct (ent_ix_in ins Ps (X0 :: Xrs) ix X Hall Hh) as (P & XP & HP & He).
        destruct (xchecks_all t img depth s0 g Ps f P XP Hck HP) as (Hok & fP & HckP & HinP).
        destruct (xent_sound ins s0 E0 ms0 P XP X ms E Hbi He Hok Hinv)
          as (E' & HdP & HiP & HfrP & HshP & HnP & HrtP & HwP & HxP).
        assert (HbP : bases_ins (vars_below (s_next P)) (s_rgs P) = true).
        { apply (bases_ins_shape (vars_below (s_next P)) (s_rgs s0)); [exact HshP|].
          apply (bases_ins_mono ins); [|exact Hbi]. intros y Hy. apply in_vars_below.
          rewrite forallb_forall in Hib. pose proof (Hib y Hy) as Y. apply Pos.ltb_lt in Y. lia. }
        destruct (check_frame_frp segs t img (vars_below (s_next P)) depth (g P) P fP Ht Himg HckP E' ms HdP (state_wf_bases _ HwP) HbP)
          as (L2 & ms2 & E2 & HL2 & Hst2 & Hd2 & Hi2 & Hfr2 & Hsh2 & Hn2 & Hrt2 & Hfp2).
        apply (IH (others ++ f) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
        exists (XST L2 XP), ms2, E2. split; [apply in_or_app; right; exact (HinP L2 HL2)|]. split; [|exact (HΦt _ _ _ HΦ (HΦfx _ _ Hfp2))].
        pose proof Hinv as ((Hst & _ & _ & Hfr & _ & _ & _) & _ & _).
        assert (Hag : agree (s_next P) E' E2).
        { intros x Hx. symmetry. apply Hi2. apply in_vars_below. exact Hx. }
        split; [|split].
        -- cbn [xs_st]. split; [eapply isteps_trans; [exact Hst | exact Hst2]|]. split; [exact Hd2|].
           split; [intros x Hx; rewrite <- (Hag x); [exact (HiP x Hx)|];
                   rewrite forallb_forall in Hib; pose proof (Hib x Hx) as Y; apply Pos.ltb_lt in Y; lia|].
           split; [intros x Hx; rewrite (Hfr2 x (HfrP x Hx)); exact (Hfr x Hx)|].
           split; [rewrite Hsh2; exact HshP|]. split; [lia|]. rewrite Hrt2; exact HrtP.
        -- cbn [xs_x]. unfold xtmpl_ok in Hok. apply andb_prop in Hok as [_ Hxw]. rewrite Forall_forall in *. intros f0 Hf0.
           rewrite forallb_forall in Hxw. exact (xfact_ok_agree _ E' E2 _ f0 (Hxw f0 Hf0) Hag (HxP f0 Hf0)).
        -- cbn [xs_x xs_st]. unfold xtmpl_ok in Hok. apply andb_prop in Hok as [_ Hxw]. apply (xwf_mono (s_next P)); [exact Hn2 | exact Hxw].
      * destruct (xcalls c (X0 :: Xrs)) as [ks|] eqn:Hw; [|discriminate].
        destruct (xcalls_in c (X0 :: Xrs) ks X Hw Hh) as (K & HK & HinK).
        assert (Hs : In (cs_p0 c, cs_q c) (xsites ((pc, XCall c) :: rest))) by (left; reflexivity).
        destruct (Hsites _ _ Hs) as (rets & Hfn).
        pose proof Hinv as ((_ & Hd & _) & _).
        destruct (call_sound_P segs Φ HΦi _ _ rets _ _ _ _ _ (xs_st X) K E ms Hfn HK Hd) as (ms2 & E2 & Hst2 & Hd2 & Ha2 & Hfr2 & HΦ2).
        destruct (call_cont_shape _ _ _ _ _ _ _ _ _ HK) as (HshK & HnK & HrtK).
        apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
        exists (XST K (xs_x X)), ms2, E2. split; [apply in_or_app; right; exact HinK|].
        split; [exact (winvx_call ins s0 E0 ms0 X K ms E ms2 E2 Hbi Hib Hinv Hst2 Hd2 Ha2 Hfr2 HshK HnK HrtK) | exact (HΦt _ _ _ HΦ HΦ2)].
      * destruct (xcalls c (X0 :: Xrs)) as [ks|] eqn:Hw; [|discriminate].
        destruct (xcalls_in c (X0 :: Xrs) ks X Hw Hh) as (K & HK & HinK).
        assert (Hs : In (cs_p0 c, cs_q c) (xksites ((pc, XCallK c) :: rest))) by (left; reflexivity).
        pose proof (Hks _ _ Hs) as Hfn.
        pose proof Hinv as ((_ & Hd & _) & _).
        destruct (call_sound_kP segs Φ HΦi _ _ _ _ _ _ _ (xs_st X) K E ms Hfn HK Hd) as (ms2 & E2 & Hst2 & Hd2 & Ha2 & Hfr2 & HΦ2).
        destruct (call_cont_shape _ _ _ _ _ _ _ _ _ HK) as (HshK & HnK & HrtK).
        apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
        exists (XST K (xs_x X)), ms2, E2. split; [apply in_or_app; right; exact HinK|].
        split; [exact (winvx_call ins s0 E0 ms0 X K ms E ms2 E2 Hbi Hib Hinv Hst2 Hd2 Ha2 Hfr2 HshK HnK HrtK) | exact (HΦt _ _ _ HΦ HΦ2)].
      * destruct (xcallsm cs (X0 :: Xrs)) as [ks|] eqn:Hw; [|discriminate].
        destruct (xcallsm_in cs (X0 :: Xrs) ks X Hw Hh) as (c & K & Hcin & HK & HinK).
        assert (Hs : In (cs_p0 c, cs_q c) (xksites ((pc, XCallKs cs) :: rest))).
        { cbn [xksites]. apply in_or_app. left. apply (in_map (fun c => (cs_p0 c, cs_q c))). exact Hcin. }
        pose proof (Hks _ _ Hs) as Hfn.
        pose proof Hinv as ((_ & Hd & _) & _).
        destruct (call_sound_kP segs Φ HΦi _ _ _ _ _ _ _ (xs_st X) K E ms Hfn HK Hd) as (ms2 & E2 & Hst2 & Hd2 & Ha2 & Hfr2 & HΦ2).
        destruct (call_cont_shape _ _ _ _ _ _ _ _ _ HK) as (HshK & HnK & HrtK).
        apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
        exists (XST K (xs_x X)), ms2, E2. split; [apply in_or_app; right; exact HinK|].
        split; [exact (winvx_call ins s0 E0 ms0 X K ms E ms2 E2 Hbi Hib Hinv Hst2 Hd2 Ha2 Hfr2 HshK HnK HrtK) | exact (HΦt _ _ _ HΦ HΦ2)].
      * destruct (xfrags c pcQ (X0 :: Xrs)) as [ks|] eqn:Hw; [|discriminate].
        destruct (xfrags_in c pcQ (X0 :: Xrs) ks X Hw Hh) as (K & HK & HinK).
        assert (Hs : In (cs_p0 c, cs_q c, pcQ) (xfsites ((pc, XFragK c pcQ) :: rest))) by (left; reflexivity).
        pose proof (Hfs _ _ _ Hs) as Hfn.
        pose proof Hinv as ((_ & Hd & _) & _).
        destruct (frag_sound_kP segs Φ HΦi _ _ _ _ _ _ _ (xs_st X) K E ms Hfn HK Hd) as (ms2 & E2 & Hst2 & Hd2 & Ha2 & Hfr2 & HΦ2).
        destruct (frag_cont_shape _ _ _ _ _ _ _ _ _ HK) as (HshK & HnK & HrtK).
        apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
        exists (XST K (xs_x X)), ms2, E2. split; [apply in_or_app; right; exact HinK|].
        split; [exact (winvx_call ins s0 E0 ms0 X K ms E ms2 E2 Hbi Hib Hinv Hst2 Hd2 Ha2 Hfr2 HshK HnK HrtK) | exact (HΦt _ _ _ HΦ HΦ2)].
      * destruct (xfragsm cs pcQ (X0 :: Xrs)) as [ks|] eqn:Hw; [|discriminate].
        destruct (xfragsm_in cs pcQ (X0 :: Xrs) ks X Hw Hh) as (c & K & Hcin & HK & HinK).
        assert (Hs : In (cs_p0 c, cs_q c, pcQ) (xfsites ((pc, XFragKs cs pcQ) :: rest))).
        { cbn [xfsites]. apply in_or_app. left. apply (in_map (fun c => (cs_p0 c, cs_q c, pcQ))). exact Hcin. }
        pose proof (Hfs _ _ _ Hs) as Hfn.
        pose proof Hinv as ((_ & Hd & _) & _).
        destruct (frag_sound_kP segs Φ HΦi _ _ _ _ _ _ _ (xs_st X) K E ms Hfn HK Hd) as (ms2 & E2 & Hst2 & Hd2 & Ha2 & Hfr2 & HΦ2).
        destruct (frag_cont_shape _ _ _ _ _ _ _ _ _ HK) as (HshK & HnK & HrtK).
        apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
        exists (XST K (xs_x X)), ms2, E2. split; [apply in_or_app; right; exact HinK|].
        split; [exact (winvx_call ins s0 E0 ms0 X K ms E ms2 E2 Hbi Hib Hinv Hst2 Hd2 Ha2 Hfr2 HshK HnK HrtK) | exact (HΦt _ _ _ HΦ HΦ2)].
      * destruct (xhands fh (X0 :: Xrs)) as [ks|] eqn:Hw; [|discriminate].
        destruct (xhands_in fh (X0 :: Xrs) ks X Hw Hh) as (Ks & HKs & HinKs).
        assert (Hs : In fh (xhandl ((pc, XHand fh) :: rest))) by (left; reflexivity).
        pose proof (Hhand _ Hs) as Hfn.
        pose proof Hinv as (Hw0 & HxF & Hxw). pose proof Hw0 as (Hst & Hd & Hi & Hfr & Hsh & Hn & Hrt).
        assert (Hm0 : forall x, fr_pt E (s_rgs (xs_st X)) x -> ms_mem ms x = ms_mem ms0 x).
        { intros x Hx. apply Hfr. exact (winv_fr_back ins s0 E0 ms0 (xs_st X) ms E x Hbi Hw0 Hx). }
        destruct (Hfn X Ks E ms (ms_mem ms0) HKs Hd HxF Hxw Hm0)
          as (K & ms2 & E2 & HinK & Hst2 & Hd2 & Ha2 & Hfr2 & HshK & HnK & HrtK & HxK & HxwK & HΦ2).
        apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
        exists K, ms2, E2. split; [apply in_or_app; right; exact (HinKs K HinK)|]. split; [|exact (HΦt _ _ _ HΦ HΦ2)].
        split; [|split; [exact HxK | exact HxwK]].
        split; [eapply isteps_trans; [exact Hst | exact Hst2]|]. split; [exact Hd2|].
        rewrite forallb_forall in Hib.
        split; [intros x Hx; rewrite <- (Ha2 x ltac:(pose proof (Hib x Hx) as Y; apply Pos.ltb_lt in Y; lia)); exact (Hi x Hx)|].
        split; [intros x Hx; rewrite (Hfr2 x (winv_fr segs ins s0 E0 ms0 (xs_st X) ms E x Hbi Hw0 Hx)); exact (Hfr x Hx)|].
        split; [rewrite HshK; exact Hsh|]. split; [lia|]. rewrite HrtK; exact Hrt.
    + (* [comment removed for export] *)
      assert (Ho : In X others) by (apply filter_In; split; [exact HX | rewrite Hpc; reflexivity]).
      destruct here as [|X0 Xrs] eqn:Hhere.
      * exact (IH others finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0 (ex_intro _ X (ex_intro _ ms (ex_intro _ E (conj Ho (conj Hinv HΦ)))))).
      * destruct a as [mk g|c|c|cs|c pcQ|cs pcQ|fh].
        -- destruct (mk (X0 :: Xrs)) as [Ps ix].
           destruct (ent_ix ins Ps (X0 :: Xrs) ix); [|discriminate].
           destruct (xchecks t img depth s0 g Ps) as [f|]; [|discriminate].
           apply (IH (others ++ f) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists X, ms, E. split; [apply in_or_app; left; exact Ho | split; [exact Hinv | exact HΦ]].
        -- destruct (xcalls c (X0 :: Xrs)) as [ks|]; [|discriminate].
           apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists X, ms, E. split; [apply in_or_app; left; exact Ho | split; [exact Hinv | exact HΦ]].
        -- destruct (xcalls c (X0 :: Xrs)) as [ks|]; [|discriminate].
           apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists X, ms, E. split; [apply in_or_app; left; exact Ho | split; [exact Hinv | exact HΦ]].
        -- destruct (xcallsm cs (X0 :: Xrs)) as [ks|]; [|discriminate].
           apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists X, ms, E. split; [apply in_or_app; left; exact Ho | split; [exact Hinv | exact HΦ]].
        -- destruct (xfrags c pcQ (X0 :: Xrs)) as [ks|]; [|discriminate].
           apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists X, ms, E. split; [apply in_or_app; left; exact Ho | split; [exact Hinv | exact HΦ]].
        -- destruct (xfragsm cs pcQ (X0 :: Xrs)) as [ks|]; [|discriminate].
           apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists X, ms, E. split; [apply in_or_app; left; exact Ho | split; [exact Hinv | exact HΦ]].
        -- destruct (xhands fh (X0 :: Xrs)) as [ks|]; [|discriminate].
           apply (IH (others ++ ks) finals Ht Himg HΦfx Hc Hs' Hh' Hk' Hf' Hbi Hib E0 ms0).
           exists X, ms, E. split; [apply in_or_app; left; exact Ho | split; [exact Hinv | exact HΦ]].
Qed.
#[using="Type"] Theorem wcheckx_sound : forall t img ins depth s0 nodes pend finals,
  tbl_ok segs t -> img_ok segs img -> wcheckx t img ins depth s0 nodes pend = Some finals ->
  (forall P0 Q, In (P0, Q) (xsites nodes) -> exists rets, fn_ok segs P0 Q rets) ->
  (forall f, In f (xhandl nodes) -> hand_okx f) ->
  (forall P0 Q, In (P0, Q) (xksites nodes) -> kfn_ok segs P0 Q) ->
  (forall P0 Q pcQ, In (P0, Q, pcQ) (xfsites nodes) -> kfrag_ok segs P0 Q pcQ) ->
  bases_ins ins (s_rgs s0) = true -> forallb (fun x => Pos.ltb x (s_next s0)) ins = true ->
  forall E0 ms0, (exists X ms E, In X pend /\ winvx ins s0 E0 ms0 X ms E) ->
  exists X ms E, In X finals /\ winvx ins s0 E0 ms0 X ms E.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth s0 nodes pend finals Ht Himg Hc Hsites Hhand Hks Hfs Hbi Hib E0 ms0 (X & ms & E & HX & Hinv).
  destruct (wcheckx_soundP (fun _ _ => True) fp_inv_true (fun _ _ _ _ _ => I) t img ins depth s0 nodes pend finals Ht Himg (fun _ _ _ => I) Hc
              (fun P0 Q H => let '(ex_intro _ rets Hf) := Hsites P0 Q H in ex_intro _ rets (fn_ok_P segs P0 Q rets Hf))
              (fun f H => hand_okx_P f (Hhand f H)) (fun P0 Q H => kfn_ok_P segs P0 Q (Hks P0 Q H))
              (fun P0 Q pcQ H => kfrag_ok_P segs P0 Q pcQ (Hfs P0 Q pcQ H)) Hbi Hib E0 ms0
              (ex_intro _ X (ex_intro _ ms (ex_intro _ E (conj HX (conj Hinv I))))))
    as (X' & ms' & E' & H1 & H2 & _).
  exists X', ms', E'. exact (conj H1 H2).
Qed.

#[using="Type"] Theorem wstartx_soundP : forall (Φ : machine_state -> machine_state -> Prop), fp_inv Φ -> (forall a b c, Φ a b -> Φ b c -> Φ a c) ->
  forall t img ins depth s0 p0 nodes finals,
  tbl_ok segs t -> img_ok segs img -> (forall a b, fpc t a b -> Φ a b) -> wstartx t img ins depth s0 p0 nodes = Some finals ->
  (forall P0 Q, In (P0, Q) (xsites nodes) -> exists rets, fn_okP segs Φ P0 Q rets) ->
  (forall f, In f (xhandl nodes) -> hand_okxP Φ f) ->
  (forall P0 Q, In (P0, Q) (xksites nodes) -> kfn_okP segs Φ P0 Q) ->
  (forall P0 Q pcQ, In (P0, Q, pcQ) (xfsites nodes) -> kfrag_okP segs Φ P0 Q pcQ) ->
  bases_wf (s_next s0) (s_rgs s0) = true -> bases_ins ins (s_rgs s0) = true -> forallb (fun x => Pos.ltb x (s_next s0)) ins = true ->
  forall E0 ms0, sden segs E0 s0 ms0 -> exists X ms E, In X finals /\ winvx ins s0 E0 ms0 X ms E /\ Φ ms0 ms.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ HΦi HΦt t img ins depth s0 p0 nodes finals Ht Himg HΦfx Hc Hsites Hhand Hks Hfs Hw Hbi Hib E0 ms0 Hd. unfold wstartx in Hc.
  destruct (check t img ins depth p0 s0) as [f|] eqn:Hck; [|discriminate].
  apply (wcheckx_soundP Φ HΦi HΦt t img ins depth s0 nodes (List.map (fun K => XST K []) f) finals Ht Himg HΦfx Hc Hsites Hhand Hks Hfs Hbi Hib E0 ms0).
  destruct (check_frame_frp segs t img ins depth p0 s0 f Ht Himg Hck E0 ms0 Hd Hw Hbi) as (L & ms & E & HL & Hst & Hd1 & Hi & Hfr & Hsh & Hn & Hrt & Hfp).
  exists (XST L []), ms, E. split; [apply in_map_iff; exists L; split; [reflexivity | exact HL]|].
  split; [|exact (HΦfx _ _ Hfp)].
  split; [|split; [constructor | reflexivity]].
  split; [exact Hst|]. split; [exact Hd1|]. split; [exact Hi|]. split; [exact Hfr|].
  split; [exact Hsh | split; [exact Hn | exact Hrt]].
Qed.
#[using="Type"] Theorem wstartx_sound : forall t img ins depth s0 p0 nodes finals,
  tbl_ok segs t -> img_ok segs img -> wstartx t img ins depth s0 p0 nodes = Some finals ->
  (forall P0 Q, In (P0, Q) (xsites nodes) -> exists rets, fn_ok segs P0 Q rets) ->
  (forall f, In f (xhandl nodes) -> hand_okx f) ->
  (forall P0 Q, In (P0, Q) (xksites nodes) -> kfn_ok segs P0 Q) ->
  (forall P0 Q pcQ, In (P0, Q, pcQ) (xfsites nodes) -> kfrag_ok segs P0 Q pcQ) ->
  bases_wf (s_next s0) (s_rgs s0) = true -> bases_ins ins (s_rgs s0) = true -> forallb (fun x => Pos.ltb x (s_next s0)) ins = true ->
  forall E0 ms0, sden segs E0 s0 ms0 -> exists X ms E, In X finals /\ winvx ins s0 E0 ms0 X ms E.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img ins depth s0 p0 nodes finals Ht Himg Hc Hsites Hhand Hks Hfs Hw Hbi Hib E0 ms0 Hd.
  destruct (wstartx_soundP (fun _ _ => True) fp_inv_true (fun _ _ _ _ _ => I) t img ins depth s0 p0 nodes finals Ht Himg (fun _ _ _ => I) Hc
              (fun P0 Q H => let '(ex_intro _ rets Hf) := Hsites P0 Q H in ex_intro _ rets (fn_ok_P segs P0 Q rets Hf))
              (fun f H => hand_okx_P f (Hhand f H)) (fun P0 Q H => kfn_ok_P segs P0 Q (Hks P0 Q H))
              (fun P0 Q pcQ H => kfrag_ok_P segs P0 Q pcQ (Hfs P0 Q pcQ H)) Hw Hbi Hib E0 ms0 Hd)
    as (X & ms & E & H1 & H2 & _).
  exists X, ms, E. exact (conj H1 H2).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem fn_ok_of_wcertxP : forall (Φ : machine_state -> machine_state -> Prop), fp_inv Φ -> (forall a b c, Φ a b -> Φ b c -> Φ a c) ->
  forall t img depth p0 nodes P0 Q rets,
  tbl_ok segs t -> img_ok segs img -> (forall a b, fpc t a b -> Φ a b) ->
  (match wstartx t img (vars_below (s_next P0)) depth P0 p0 nodes with
   | Some l => forallb (fun X => fin_q Q rets (s_next P0) (xs_st X)) l | None => false end) = true ->
  (forall P0' Q', In (P0', Q') (xsites nodes) -> exists rets', fn_okP segs Φ P0' Q' rets') ->
  (forall f, In f (xhandl nodes) -> hand_okxP Φ f) ->
  (forall P0' Q', In (P0', Q') (xksites nodes) -> kfn_okP segs Φ P0' Q') ->
  (forall P0' Q' pcQ, In (P0', Q', pcQ) (xfsites nodes) -> kfrag_okP segs Φ P0' Q' pcQ) ->
  bases_wf (s_next P0) (s_rgs P0) = true -> bases_ins (vars_below (s_next P0)) (s_rgs P0) = true -> state_wf Q = true ->
  Forall (is_ret segs) rets -> fn_okP segs Φ P0 Q rets.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ HΦi HΦt t img depth p0 nodes P0 Q rets Ht Himg HΦfx Hc Hsites Hhand Hks Hfs Hw1 Hw2 HwQ Hrets E ms Hd.
  destruct (wstartx t img (vars_below (s_next P0)) depth P0 p0 nodes) as [finals|] eqn:Hck; [|discriminate].
  assert (Hib : forallb (fun x => Pos.ltb x (s_next P0)) (vars_below (s_next P0)) = true).
  { apply forallb_forall. intros x Hx. apply Pos.ltb_lt. exact (vars_below_lt _ x Hx). }
  destruct (wstartx_soundP Φ HΦi HΦt t img (vars_below (s_next P0)) depth P0 p0 nodes finals Ht Himg HΦfx Hck Hsites Hhand Hks Hfs Hw1 Hw2 Hib E ms Hd)
    as (X & ms' & E1 & HX & ((Hst & Hd1 & Hins & Hfr & _ & _ & _) & _) & HΦ1).
  rewrite forallb_forall in Hc. pose proof (Hc X HX) as HfL. unfold fin_q in HfL.
  set (L := xs_st X) in *.
  set (σ := mq L (with_pc Q (s_pc L))) in HfL.
  apply andb_prop in HfL as [HfL Hfix]. apply andb_prop in HfL as [HfL Hent]. apply andb_prop in HfL as [Hp Hr].
  apply existsb_exists in Hp as (p0' & Hp0 & Hpe). apply Z.eqb_eq in Hpe.
  exists ms', (ecomp E1 σ), (s_pc L). split; [exact Hst|]. split; [rewrite Hpe; exact Hp0|].
  split; [rewrite Forall_forall in Hrets; apply Hrets; rewrite Hpe; exact Hp0|].
  split; [apply (entails_sden segs E1 L (with_pc Q (s_pc L)) σ ms' (sden_0 _ _ _ _ Hd1) Hent); rewrite state_wf_with_pc; exact HwQ|].
  split; [|split; [exact Hfr | exact HΦ1]].
  intros x Hx. rewrite <- (fixed_below_agree E1 σ (s_next P0) Hfix x Hx). symmetry. apply Hins. apply in_vars_below. exact Hx.
Qed.
#[using="Type"] Theorem fn_ok_of_wcertx : forall t img depth p0 nodes P0 Q rets,
  tbl_ok segs t -> img_ok segs img ->
  (match wstartx t img (vars_below (s_next P0)) depth P0 p0 nodes with
   | Some l => forallb (fun X => fin_q Q rets (s_next P0) (xs_st X)) l | None => false end) = true ->
  (forall P0' Q', In (P0', Q') (xsites nodes) -> exists rets', fn_ok segs P0' Q' rets') ->
  (forall f, In f (xhandl nodes) -> hand_okx f) ->
  (forall P0' Q', In (P0', Q') (xksites nodes) -> kfn_ok segs P0' Q') ->
  (forall P0' Q' pcQ, In (P0', Q', pcQ) (xfsites nodes) -> kfrag_ok segs P0' Q' pcQ) ->
  bases_wf (s_next P0) (s_rgs P0) = true -> bases_ins (vars_below (s_next P0)) (s_rgs P0) = true -> state_wf Q = true ->
  Forall (is_ret segs) rets -> fn_ok segs P0 Q rets.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img depth p0 nodes P0 Q rets Ht Himg Hc Hsites Hhand Hks Hfs Hw1 Hw2 HwQ Hrets.
  apply (fn_okP_ok segs (fun _ _ => True)).
  exact (fn_ok_of_wcertxP (fun _ _ => True) fp_inv_true (fun _ _ _ _ _ => I) t img depth p0 nodes P0 Q rets Ht Himg (fun _ _ _ => I) Hc
              (fun P0' Q' H => let '(ex_intro _ rets' Hf) := Hsites P0' Q' H in ex_intro _ rets' (fn_ok_P segs P0' Q' rets' Hf))
              (fun f H => hand_okx_P f (Hhand f H)) (fun P0' Q' H => kfn_ok_P segs P0' Q' (Hks P0' Q' H))
              (fun P0' Q' pcQ H => kfrag_ok_P segs P0' Q' pcQ (Hfs P0' Q' pcQ H)) Hw1 Hw2 HwQ Hrets).
Qed.
(* [comment removed for export] *)
#[using="Type"] Theorem fn_ok_fp_of_wcertx : forall t img depth p0 nodes P0 Q rets,
  tbl_ok segs t -> img_ok segs img -> tbl_nofp t = true ->
  (match wstartx t img (vars_below (s_next P0)) depth P0 p0 nodes with
   | Some l => forallb (fun X => fin_q Q rets (s_next P0) (xs_st X)) l | None => false end) = true ->
  (forall P0' Q', In (P0', Q') (xsites nodes) -> exists rets', fn_ok_fp segs P0' Q' rets') ->
  (forall f, In f (xhandl nodes) -> hand_okx_fp f) ->
  (forall P0' Q', In (P0', Q') (xksites nodes) -> kfn_ok_fp segs P0' Q') ->
  (forall P0' Q' pcQ, In (P0', Q', pcQ) (xfsites nodes) -> kfrag_ok_fp segs P0' Q' pcQ) ->
  bases_wf (s_next P0) (s_rgs P0) = true -> bases_ins (vars_below (s_next P0)) (s_rgs P0) = true -> state_wf Q = true ->
  Forall (is_ret segs) rets -> fn_ok_fp segs P0 Q rets.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img depth p0 nodes P0 Q rets Ht Himg Hnf. apply (fn_ok_of_wcertxP fpeq fp_inv_fpeq fpeq_trans t img depth p0 nodes P0 Q rets Ht Himg).
  intros a b H. exact (H Hnf).
Qed.

(* [comment removed for export] *)
#[using="Type"] Theorem kfrag_ok_of_wcertxP : forall (Φ : machine_state -> machine_state -> Prop), fp_inv Φ -> (forall a b c, Φ a b -> Φ b c -> Φ a c) ->
  forall t img depth p0 nodes P0 Q pcQ,
  tbl_ok segs t -> img_ok segs img -> (forall a b, fpc t a b -> Φ a b) ->
  (match wstartx t img (vars_below (s_next P0)) depth P0 p0 nodes with
   | Some l => forallb (fun X => fin_q Q [pcQ] (s_next P0) (xs_st X)) l | None => false end) = true ->
  (forall P0' Q', In (P0', Q') (xsites nodes) -> exists rets', fn_okP segs Φ P0' Q' rets') ->
  (forall f, In f (xhandl nodes) -> hand_okxP Φ f) ->
  (forall P0' Q', In (P0', Q') (xksites nodes) -> kfn_okP segs Φ P0' Q') ->
  (forall P0' Q' pcQ', In (P0', Q', pcQ') (xfsites nodes) -> kfrag_okP segs Φ P0' Q' pcQ') ->
  bases_wf (s_next P0) (s_rgs P0) = true -> bases_ins (vars_below (s_next P0)) (s_rgs P0) = true -> state_wf Q = true ->
  kfrag_okP segs Φ P0 Q pcQ.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros Φ HΦi HΦt t img depth p0 nodes P0 Q pcQ Ht Himg HΦfx Hc Hsites Hhand Hks Hfs Hw1 Hw2 HwQ E ms Hd.
  destruct (wstartx t img (vars_below (s_next P0)) depth P0 p0 nodes) as [finals|] eqn:Hck; [|discriminate].
  assert (Hib : forallb (fun x => Pos.ltb x (s_next P0)) (vars_below (s_next P0)) = true).
  { apply forallb_forall. intros x Hx. apply Pos.ltb_lt. exact (vars_below_lt _ x Hx). }
  destruct (wstartx_soundP Φ HΦi HΦt t img (vars_below (s_next P0)) depth P0 p0 nodes finals Ht Himg HΦfx Hck Hsites Hhand Hks Hfs Hw1 Hw2 Hib E ms Hd)
    as (X & ms' & E1 & HX & ((Hst & Hd1 & Hins & Hfr & _ & _ & _) & _) & HΦ1).
  rewrite forallb_forall in Hc. pose proof (Hc X HX) as HfL. unfold fin_q in HfL.
  set (L := xs_st X) in *.
  set (σ := mq L (with_pc Q (s_pc L))) in HfL.
  apply andb_prop in HfL as [HfL Hfix]. apply andb_prop in HfL as [HfL Hent]. apply andb_prop in HfL as [Hp Hr].
  apply existsb_exists in Hp as (p0' & Hp0 & Hpe). apply Z.eqb_eq in Hpe.
  destruct Hp0 as [Hp0|[]]. subst p0'.
  exists ms', (ecomp E1 σ). split; [exact Hst|].
  split; [rewrite <- Hpe; apply (entails_sden segs E1 L (with_pc Q (s_pc L)) σ ms' (sden_0 _ _ _ _ Hd1) Hent); rewrite state_wf_with_pc; exact HwQ|].
  split; [|split; [exact Hfr | exact HΦ1]].
  intros x Hx. rewrite <- (fixed_below_agree E1 σ (s_next P0) Hfix x Hx). symmetry. apply Hins. apply in_vars_below. exact Hx.
Qed.
#[using="Type"] Theorem kfrag_ok_of_wcertx : forall t img depth p0 nodes P0 Q pcQ,
  tbl_ok segs t -> img_ok segs img ->
  (match wstartx t img (vars_below (s_next P0)) depth P0 p0 nodes with
   | Some l => forallb (fun X => fin_q Q [pcQ] (s_next P0) (xs_st X)) l | None => false end) = true ->
  (forall P0' Q', In (P0', Q') (xsites nodes) -> exists rets', fn_ok segs P0' Q' rets') ->
  (forall f, In f (xhandl nodes) -> hand_okx f) ->
  (forall P0' Q', In (P0', Q') (xksites nodes) -> kfn_ok segs P0' Q') ->
  (forall P0' Q' pcQ', In (P0', Q', pcQ') (xfsites nodes) -> kfrag_ok segs P0' Q' pcQ') ->
  bases_wf (s_next P0) (s_rgs P0) = true -> bases_ins (vars_below (s_next P0)) (s_rgs P0) = true -> state_wf Q = true ->
  kfrag_ok segs P0 Q pcQ.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img depth p0 nodes P0 Q pcQ Ht Himg Hc Hsites Hhand Hks Hfs Hw1 Hw2 HwQ.
  apply (kfrag_okP_ok segs (fun _ _ => True)).
  exact (kfrag_ok_of_wcertxP (fun _ _ => True) fp_inv_true (fun _ _ _ _ _ => I) t img depth p0 nodes P0 Q pcQ Ht Himg (fun _ _ _ => I) Hc
              (fun P0' Q' H => let '(ex_intro _ rets' Hf) := Hsites P0' Q' H in ex_intro _ rets' (fn_ok_P segs P0' Q' rets' Hf))
              (fun f H => hand_okx_P f (Hhand f H)) (fun P0' Q' H => kfn_ok_P segs P0' Q' (Hks P0' Q' H))
              (fun P0' Q' pcQ' H => kfrag_ok_P segs P0' Q' pcQ' (Hfs P0' Q' pcQ' H)) Hw1 Hw2 HwQ).
Qed.
(* [comment removed for export] *)
#[using="Type"] Theorem kfrag_ok_fp_of_wcertx : forall t img depth p0 nodes P0 Q pcQ,
  tbl_ok segs t -> img_ok segs img -> tbl_nofp t = true ->
  (match wstartx t img (vars_below (s_next P0)) depth P0 p0 nodes with
   | Some l => forallb (fun X => fin_q Q [pcQ] (s_next P0) (xs_st X)) l | None => false end) = true ->
  (forall P0' Q', In (P0', Q') (xsites nodes) -> exists rets', fn_ok_fp segs P0' Q' rets') ->
  (forall f, In f (xhandl nodes) -> hand_okx_fp f) ->
  (forall P0' Q', In (P0', Q') (xksites nodes) -> kfn_ok_fp segs P0' Q') ->
  (forall P0' Q' pcQ', In (P0', Q', pcQ') (xfsites nodes) -> kfrag_ok_fp segs P0' Q' pcQ') ->
  bases_wf (s_next P0) (s_rgs P0) = true -> bases_ins (vars_below (s_next P0)) (s_rgs P0) = true -> state_wf Q = true ->
  kfrag_ok_fp segs P0 Q pcQ.
Proof. LiaFast.lf_pins LiaFast.u0.
  intros t img depth p0 nodes P0 Q pcQ Ht Himg Hnf. apply (kfrag_ok_of_wcertxP fpeq fp_inv_fpeq fpeq_trans t img depth p0 nodes P0 Q pcQ Ht Himg).
  intros a b H. exact (H Hnf).
Qed.
End WSoundX.
