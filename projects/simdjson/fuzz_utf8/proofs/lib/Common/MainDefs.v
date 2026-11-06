(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import MemImageType.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec AxSymExec3 AsanPlanCore AsanPlan AsanPlanSound. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import AsanNodesArg AsanNodesIO AsanMainLib ImgParams MallocNodes2 AsanNodesRP ExecNodes ExecNodesW LinkNodes MoveNodes SmearNode FactGcNode MinifyGhost ParserGhost.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AP.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition KCm : nat := 0.
Definition BFUELm : nat := 400000.

(* [comment removed for export] *)
Lemma APC_NX0_min : APS.nx0_min_ok NX0.
Proof. unfold APS.nx0_min_ok, NX0. lia. Qed.

(* [comment removed for export] *)
Section Hooks.
  Context {fx : FPState}.
  Variable ip : imgparams.

  (* [comment removed for export] *)
  Definition XN0 (id : nat) (args : list expr) (cs : acs) : option acs := None.
  Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
  Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

  (* [comment removed for export] *)
  Definition XNp (IT : itab) (T : ION.iotab) (id : nat) (args : list expr) (cs : acs) : option acs :=
    if (id <? 10)%nat then
      (if ((id =? 0)%nat && (AN.g_istrlen (ip_G ip) =? 0))%bool then None
       else AN.xn (ip_segs ip) (ip_A ip) NX0 (ip_G ip) id args cs)
    else if ((id =? 20)%nat || (id =? 21)%nat)%bool then None   (* [comment removed for export] *)
    else if ((40 <=? id)%nat && (id <? 50)%nat)%bool then EXW.xn (ip_segs ip) IT NX0 id args cs
    else if (id <? 90)%nat then ION.xn (ip_segs ip) T id args cs
    else if (((id =? 100)%nat || (id =? 101)%nat) && negb (RPN.rp_entry (ip_RP ip) =? 0))%bool
         then RPN.xn (ip_segs ip) NX0 (ip_RP ip) id args cs     (* [comment removed for export] *)
    else if (id =? 110)%nat then LNK.xn args cs                        (* [comment removed for export] *)
    else if (id =? 111)%nat then MVN.xn IT (ip_A ip) args cs           (* [comment removed for export] *)
    else if (id =? 113)%nat then SMR.xn args cs                        (* [comment removed for export] *)
    else if (id =? 115)%nat then xn_visfoot (ip_A ip) (ip_limit ip) args cs   (* [comment removed for export] *)
    else if (id =? 117)%nat then FGC.xn args cs                        (* [comment removed for export] *)
    else None.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition XNmV (IT : itab) (GV : list APC.vc) (T : ION.iotab) (id : nat) (args : list expr) (cs : acs) : option acs :=
    if (id <? 10)%nat then
      (if ((id =? 0)%nat && (AN.g_istrlen (ip_G ip) =? 0))%bool then None
       else AN.xn (ip_segs ip) (ip_A ip) NX0 (ip_G ip) id args cs)
    else if ((id =? 20)%nat || (id =? 21)%nat)%bool then MN2.xn (ip_segs ip) (ip_A ip) NX0 (ip_M ip) (PGA.Gparse GV) id args cs   (* [comment removed for export] *)
    else if ((40 <=? id)%nat && (id <? 50)%nat)%bool then EXW.xn (ip_segs ip) IT NX0 id args cs
    else if (id <? 90)%nat then ION.xn (ip_segs ip) T id args cs
    else if (((id =? 100)%nat || (id =? 101)%nat) && negb (RPN.rp_entry (ip_RP ip) =? 0))%bool
         then RPN.xn (ip_segs ip) NX0 (ip_RP ip) id args cs     (* [comment removed for export] *)
    else if (id =? 110)%nat then LNK.xn args cs                        (* [comment removed for export] *)
    else if (id =? 111)%nat then MVN.xn IT (ip_A ip) args cs           (* [comment removed for export] *)
    else if (id =? 113)%nat then SMR.xn args cs                        (* [comment removed for export] *)
    else if (id =? 115)%nat then xn_visfoot (ip_A ip) (ip_limit ip) args cs   (* [comment removed for export] *)
    else if (id =? 117)%nat then FGC.xn args cs                        (* [comment removed for export] *)
    else None.
  Definition XNm (IT : itab) (T : ION.iotab) (id : nat) (args : list expr) (cs : acs) : option acs := XNmV IT [] T id args cs.
  Definition XEp (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) :=
    AN.xe (ip_segs ip) (ip_A ip) NX0 (ip_G ip) id args cs.
  (* [comment removed for export] *)
  Definition xnp_extF (id : nat) : bool :=      (* [comment removed for export] *)
    ((id =? 16) || (id =? 18) || (id =? 19) || (id =? 22) || (id =? 23) || (id =? 24) || ((40 <=? id) && (id <? 50)) || (id =? 111))%nat%bool.
  (* [comment removed for export] *)
  Definition xnp_ws (id : nat) (args : list expr) (cs : acs) : option (list (saddr * expr)) :=
    if ((10 <=? id) && (id <? 20))%nat%bool then ION.xn_ws id args cs else None.
  (* [comment removed for export] *)
  Record segtab : Type := ST { st_defs : nat -> option segdef; st_vcs : list APC.vc }.
  Definition XPv (S : segtab) : xparams :=
    XP (st_defs S) None xnp_extF (PGA.Gparse (st_vcs S)) MN2.extG_m AP.sys_ws_std xnp_ws AN.xe_ws AP.x_ws_std false.   (* [comment removed for export] *)   (* [comment removed for export] *)
  Definition XPm (SG : nat -> option segdef) : xparams := XPv (ST SG []).
  (* [comment removed for export] *)
  Definition T0 : ION.iotab := ION.iot_simple ION.ONone 0%nat.
  Definition XBp (T : ION.iotab) (id : nat) (args : list expr) (cs : acs) : option (acs * acs) :=
    ION.xb (ip_segs ip) NX0 T id args cs.
End Hooks.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition htab : Type := list (nat * (acs * shape)).
Fixpoint ht_of (HT : htab) (h : nat) : option (acs * shape) :=
  match HT with [] => None | (j, e) :: HT' => if Nat.eqb j h then Some e else ht_of HT' h end.
(* [comment removed for export] *)
Definition hs_of (HT : htab) (h : nat) : option acs :=
  match ht_of HT h with Some e => Some (fst e) | None => None end.
(* [comment removed for export] *)
Definition sh_of (HT : htab) (h : nat) : option shape :=
  match ht_of HT h with Some e => Some (snd e) | None => None end.
Fixpoint lookupT {X : Type} (PT : list (nat * X)) (h : nat) : option X :=
  match PT with [] => None | (j, t) :: PT' => if Nat.eqb j h then Some t else lookupT PT' h end.

Lemma ht_of_In : forall HT h e, ht_of HT h = Some e -> In (h, e) HT.
Proof.
  induction HT as [|[j c] HT IH]; intros h e H; cbn [ht_of] in H; [discriminate|].
  destruct (Nat.eqb_spec j h); [injection H as <-; subst; left; reflexivity | right; apply IH; exact H].
Qed.
Lemma lookupT_In {X} : forall (PT : list (nat * X)) h t, lookupT PT h = Some t -> In (h, t) PT.
Proof.
  induction PT as [|[j c] PT IH]; intros h t H; cbn [lookupT] in H; [discriminate|].
  destruct (Nat.eqb_spec j h); [injection H as <-; subst; left; reflexivity | right; apply IH; exact H].
Qed.

(* [comment removed for export] *)
Section Forms.
  Context {fx : FPState}.

  (* [comment removed for export] *)
  Definition pay_start (ch : acs) (C : class) : acs := set_kn ch (facts_of_class C ++ kn ch).

  (* [comment removed for export] *)
  Definition ebounds (k : list kentry) (e : expr) : Z * Z :=
    match erange k e with Some p => p | None => (0, two64 - 1) end.
  Definition mcase_lo (ch : acs) (e : expr) (mid : Z) : acs :=
    let b := ebounds (kn ch) e in set_kn ch (KRange e (fst b) (Z.min mid (snd b)) :: kn ch).
  Definition mcase_hi (ch : acs) (e : expr) (mid : Z) : acs :=
    let b := ebounds (kn ch) e in set_kn ch (KRange e (Z.max (mid + 1) (fst b)) (snd b) :: kn ch).

  Variable ip : imgparams.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition seg_checkV (IT : itab) (S : segtab) (fuel : nat) (HS : nat -> option acs) (ch : acs) (C : class) (p : plan) : cres :=
    check (ip_segs ip) IT (ip_A ip) NX0 (ip_limit ip)
          (XNmV ip IT (st_vcs S) (iotab_of C)) (XEp ip) (XBp ip (iotab_of C)) HS KCm (XPv S) BFUELm fuel None (pay_start ch C) p.
  Definition seg_check (IT : itab) (SG : nat -> option segdef) (fuel : nat) (HS : nat -> option acs) (ch : acs) (C : class) (p : plan) : cres :=
    seg_checkV IT (ST SG []) fuel HS ch C p.
  (* [comment removed for export] *)
  Definition segs_okV (IT : itab) (S : segtab) : Prop :=
    forall sid SD, st_defs S sid = Some SD ->
      seg_ok (ip_segs ip) IT (ip_A ip) NX0 (ip_limit ip) (XNp ip IT T0) (XEp ip) (XBp ip T0) KCm (XPv S) sid SD = true.   (* [comment removed for export] *)
  Definition segs_ok (IT : itab) (SG : nat -> option segdef) : Prop := segs_okV IT (ST SG []).
  Lemma segs_ok_none : forall IT, segs_ok IT (fun _ => None).
  Proof. intros IT sid SD H. discriminate H. Qed.
  (* [comment removed for export] *)
  Definition gv_ok (S : segtab) : Prop := Forall (APS.vc_holds (ip_segs ip) (PGA.GPall (ip_segs ip))) (st_vcs S).
  Lemma gv_ok_nil : forall SG, gv_ok (ST SG []).
  Proof. intros SG. apply Forall_nil. Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition XNs (IT : itab) (id : nat) (args : list expr) (cs : acs) : option acs :=
    if (id =? 110)%nat then LNK.xn args cs
    else if ((40 <=? id)%nat && (id <? 50)%nat)%bool then EXW.xn (ip_segs ip) IT NX0 id args cs
    else if (((id =? 100)%nat || (id =? 101)%nat) && negb (RPN.rp_entry (ip_RP ip) =? 0))%bool
         then RPN.xn (ip_segs ip) NX0 (ip_RP ip) id args cs     (* [comment removed for export] *)
    else if (id =? 113)%nat then SMR.xn args cs                        (* [comment removed for export] *)
    else if (id =? 115)%nat then xn_visfoot (ip_A ip) (ip_limit ip) args cs   (* [comment removed for export] *)
    else if (id =? 117)%nat then FGC.xn args cs                        (* [comment removed for export] *)
    else None.
  (* [comment removed for export] *)
  Definition startup_check (IT : itab) (fuel : nat) (HS : nat -> option acs) (p : plan) : cres :=
    check (ip_segs ip) IT (ip_A ip) NX0 (ip_limit ip)
          (XNs IT) XE0 XB0 HS KCm XPS BFUELm fuel None (init_acs_of (ip_A ip)) p.   (* [comment removed for export] *)
End Forms.

(* [comment removed for export] *)
Strategy expand [XNm XPm seg_check segs_ok].

(* [comment removed for export] *)
Lemma itab_sound_of_eq : forall segs (IT : itab) (rs : list (Z * nat)),
  IT = mk_itab_ranges segs rs -> itab_sound segs IT.
Proof. intros segs IT rs ->. apply APS.mk_itab_ranges_sound. Qed.
