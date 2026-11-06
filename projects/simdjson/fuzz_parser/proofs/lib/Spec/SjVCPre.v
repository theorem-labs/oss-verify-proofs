(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module VP.

(* [comment removed for export] *)
Definition lsubx (a b : lin) : lin := (fst a - fst b, SLin.zadd_ts (snd a) (SLin.zscale_ts (-1) (snd b))).
Definition laddx (a b : lin) : lin := (fst a + fst b, SLin.zadd_ts (snd a) (snd b)).
Definition laddc (a : lin) (k : Z) : lin := (fst a + k, snd a).

(* [comment removed for export] *)
Inductive zf : Type :=
| ZFrng (l : lin) (lo hi : Z)      (* [comment removed for export] *)
| ZFge (l : lin)                   (* [comment removed for export] *)
| ZFeq (l : lin)                   (* [comment removed for export] *)
| ZFne (l : lin)                   (* [comment removed for export] *)
| ZFor (f g : zf).

(* [comment removed for export] *)
Definition disj (A B : Prop) : Prop := A \/ B.

(* [comment removed for export] *)
Section Den.
Variable E : env.
Definition pterm (t : Z * expr) : Z := if Z.eqb (fst t) 1 then uE E (snd t) else fst t * uE E (snd t).
Fixpoint psum (ts : list (Z * expr)) : Z :=
  match ts with [] => 0 | [t] => pterm t | t :: r => pterm t + psum r end.
Definition pden (l : lin) : Z :=
  match snd l with [] => fst l | _ => if Z.eqb (fst l) 0 then psum (snd l) else psum (snd l) + fst l end.

Lemma pterm_ok : forall t, pterm t = fst t * uE E (snd t).
Proof. intros [k a]. unfold pterm. cbn [fst snd]. destruct (Z.eqb k 1) eqn:H; [apply Z.eqb_eq in H; subst; lia| reflexivity]. Qed.
Lemma psum_ok : forall ts, psum ts = tden E ts.
Proof.
  induction ts as [|t r IH]; [reflexivity|]. destruct r as [|t' r'].
  - cbn [psum tden]. destruct t as [k a]. rewrite pterm_ok. cbn [fst snd]. lia.
  - change (psum (t :: t' :: r')) with (pterm t + psum (t' :: r')). rewrite IH. destruct t as [k a]. rewrite pterm_ok. reflexivity.
Qed.
Lemma pden_ok : forall l, pden l = fst l + tden E (snd l).
Proof.
  intros [c ts]. unfold pden. cbn [fst snd]. destruct ts as [|t r]; [cbn [tden]; lia|].
  destruct (Z.eqb c 0) eqn:H; rewrite psum_ok; [apply Z.eqb_eq in H; subst; lia| lia].
Qed.

Fixpoint zf_den (f : zf) : Prop :=
  match f with
  | ZFrng l lo hi => lo <= pden l <= hi
  | ZFge l => 0 <= pden l
  | ZFeq l => pden l = 0
  | ZFne l => pden l <> 0
  | ZFor f g => disj (zf_den f) (zf_den g)
  end.

Lemma ld_sub : forall a b, fst (lsubx a b) + tden E (snd (lsubx a b)) = (fst a + tden E (snd a)) - (fst b + tden E (snd b)).
Proof. intros [ca ta] [cb tb]. unfold lsubx. cbn [fst snd]. rewrite SLin.zadd_den, SLin.zscale_den. lia. Qed.
Lemma ld_add : forall a b, fst (laddx a b) + tden E (snd (laddx a b)) = (fst a + tden E (snd a)) + (fst b + tden E (snd b)).
Proof. intros [ca ta] [cb tb]. unfold laddx. cbn [fst snd]. rewrite SLin.zadd_den. lia. Qed.
Lemma ld_addc : forall a k, fst (laddc a k) + tden E (snd (laddc a k)) = (fst a + tden E (snd a)) + k.
Proof. intros [ca ta] k. unfold laddc. cbn [fst snd]. lia. Qed.
End Den.

(* [comment removed for export] *)
Definition atoms_var (ts : list (Z * expr)) : bool := forallb (fun t => match snd t with EVar _ => true | _ => false end) ts.

Fixpoint kdigest (allkn kn : list kentry) : list zf :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      if (atoms_var (snd (lin_of e)) && fact_nowrap allkn e hi)%bool then ZFrng (lin_of e) lo hi :: kdigest allkn rest
      else kdigest allkn rest
  | KDisj a1 n1 a2 n2 :: rest =>
      if (lin_nowrap allkn (a_base a1) && lin_nowrap allkn n1 && lin_nowrap allkn (a_base a2) && lin_nowrap allkn n2)%bool then
        let s1 := laddc (lin_of (a_base a1)) (a_off a1) in let s2 := laddc (lin_of (a_base a2)) (a_off a2) in
        ZFor (ZFge (lsubx s2 (laddx s1 (lin_of n1)))) (ZFge (lsubx s1 (laddx s2 (lin_of n2)))) :: kdigest allkn rest
      else kdigest allkn rest
  | _ :: rest => kdigest allkn rest
  end.

(* [comment removed for export] *)
Fixpoint ts_eqb (a b : list (Z * expr)) : bool :=
  match a, b with
  | [], [] => true
  | (k, x) :: a', (k', y) :: b' => (Z.eqb k k' && expr_eqb x y && ts_eqb a' b')%bool
  | _, _ => false
  end.
Lemma ts_eqb_eq : forall a b, ts_eqb a b = true -> a = b.
Proof.
  induction a as [|[k x] a IH]; intros [|[k' y] b] H; cbn [ts_eqb] in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1. apply expr_eqb_eq in H2.
  apply IH in H3. subst. reflexivity.
Qed.
Fixpoint zins_rng (ts : list (Z * expr)) (lo hi : Z) (acc : list zf) : list zf :=
  match acc with
  | [] => [ZFrng (0, ts) lo hi]
  | ZFrng (Z0, ts') lo' hi' :: r =>
      if ts_eqb ts ts' then ZFrng (0, ts') (Z.max lo lo') (Z.min hi hi') :: r else ZFrng (0, ts') lo' hi' :: zins_rng ts lo hi r
  | f :: r => f :: zins_rng ts lo hi r
  end.
Definition zadd (f : zf) (acc : list zf) : list zf :=
  match f with ZFrng (c, ts) lo hi => zins_rng ts (lo - c) (hi - c) acc | _ => acc ++ [f] end.
Definition kmerge (l : list zf) : list zf := fold_left (fun acc f => zadd f acc) l [].

Definition bdig (allkn : list kentry) (t : bool) (c : branch_cond) (a b : expr) : option zf :=
  if (lin_nowrap allkn a && lin_nowrap allkn b)%bool then
    let la := lin_of a in let lb := lin_of b in
    match c, t with
    | BC_EQ, true | BC_NE, false => Some (ZFeq (lsubx la lb))
    | BC_EQ, false | BC_NE, true => Some (ZFne (lsubx la lb))
    | BC_LTU, true | BC_GEU, false => Some (ZFge (laddc (lsubx lb la) (-1)))
    | BC_LTU, false | BC_GEU, true => Some (ZFge (lsubx la lb))
    | _, _ => None
    end
  else None.

Fixpoint pdigest (allkn : list kentry) (p : list sidecond) : list zf :=
  match p with
  | [] => []
  | SCBr t c a b :: r => match bdig allkn t c a b with Some f => f :: pdigest allkn r | None => pdigest allkn r end
  | _ :: r => pdigest allkn r
  end.

Definition digested (allkn : list kentry) (s : sidecond) : bool :=
  match s with SCBr t c a b => match bdig allkn t c a b with Some _ => true | None => false end | _ => false end.
Definition pleft (allkn : list kentry) (p : list sidecond) : list sidecond := List.filter (fun s => negb (digested allkn s)) p.

(* [comment removed for export] *)
Section Sound.
Variable segs : list Segment.
Variable E : env.
Variable M : word -> option byte.

Lemma u_lin : forall kn e, know_ok segs E M kn -> lin_nowrap kn e = true ->
  bv_unsigned (edenot E e) = pden E (lin_of e).
Proof. intros kn e HK H. rewrite pden_ok. exact (lin_nowrap_sound segs E M kn e HK H). Qed.

Lemma v_addi_alu : forall (x : word) k, bv_unsigned (v_addi x k) = bv_unsigned (alu64 ALU_ADD x (Z_to_bv 64 k)).
Proof.
  intros x k. unfold v_addi, alu64, alu. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Zplus_mod_idemp_r. reflexivity.
Qed.

Lemma u_adenot_lin : forall kn a, know_ok segs E M kn -> lin_nowrap kn (EAlu ALU_ADD (a_base a) (ELit (a_off a))) = true ->
  bv_unsigned (adenot E a) = pden E (lin_of (EAlu ALU_ADD (a_base a) (ELit (a_off a)))).
Proof.
  intros kn a HK H. unfold adenot. rewrite v_addi_alu. rewrite <- (u_lin kn _ HK H). reflexivity.
Qed.

Lemma u_lin' : forall kn e l, know_ok segs E M kn -> lin_nowrap kn e = true -> lin_of e = l -> bv_unsigned (edenot E e) = pden E l.
Proof. intros kn e l HK H <-. exact (u_lin kn e HK H). Qed.
Lemma u_adenot_lin' : forall kn a l, know_ok segs E M kn -> lin_nowrap kn (EAlu ALU_ADD (a_base a) (ELit (a_off a))) = true ->
  lin_of (EAlu ALU_ADD (a_base a) (ELit (a_off a))) = l -> bv_unsigned (adenot E a) = pden E l.
Proof. intros kn a l HK H <-. exact (u_adenot_lin kn a HK H). Qed.

Lemma kdigest_sound : forall allkn kn, know_ok segs E M allkn -> know_ok segs E M kn -> Forall (zf_den E) (kdigest allkn kn).
Proof.
  intros allkn kn HA. induction kn as [|K rest IH]; intros HK; cbn [kdigest]; [constructor|].
  apply Forall_cons_iff in HK as [HK1 HR]. specialize (IH HR).
  destruct K as [a w v|a n|a n k|lo hi|e m|e lo hi|a n|a1 n1 a2 n2|a n c|a n]; try exact IH.
  - destruct (atoms_var (snd (lin_of e)) && fact_nowrap allkn e hi)%bool eqn:C; [|exact IH].
    apply andb_prop in C as [_ C]. constructor; [|exact IH]. cbn [zf_den]. cbn [kentry_ok] in HK1.
    pose proof (fact_nowrap_sound segs E M allkn e lo hi HA C HK1) as Q. rewrite pden_ok, <- Q. exact HK1.
  - destruct (lin_nowrap allkn (a_base a1) && lin_nowrap allkn n1 && lin_nowrap allkn (a_base a2) && lin_nowrap allkn n2)%bool eqn:C;
      [|exact IH].
    repeat match type of C with (_ && _)%bool = true => apply andb_prop in C; destruct C as [C ?] end.
    constructor; [|exact IH]. cbn [zf_den kentry_ok] in *. unfold disj. rewrite !pden_ok, !ld_sub, !ld_add, !ld_addc.
    pose proof (lin_nowrap_sound segs E M allkn _ HA C) as Q1.
    repeat match goal with H : lin_nowrap allkn ?x = true |- _ => pose proof (lin_nowrap_sound segs E M allkn _ HA H); clear H end.
    unfold estart, elenZ in HK1. lia.
Qed.

Lemma zins_rng_sound : forall ts lo hi acc, lo <= tden E ts <= hi -> Forall (zf_den E) acc -> Forall (zf_den E) (zins_rng ts lo hi acc).
Proof.
  intros ts lo hi acc H. induction acc as [|f r IH]; intros HA; cbn [zins_rng].
  - constructor; [|constructor]. cbn [zf_den]. rewrite pden_ok. cbn [fst snd]. lia.
  - apply Forall_cons_iff in HA as [Hf Hr].
    destruct f as [[c ts'] lo' hi'| | | |]; try (constructor; [exact Hf| exact (IH Hr)]).
    destruct c; try (constructor; [exact Hf| exact (IH Hr)]).
    destruct (ts_eqb ts ts') eqn:Q.
    + apply ts_eqb_eq in Q. subst ts'. constructor; [|exact Hr]. cbn [zf_den] in *. rewrite pden_ok in *. cbn [fst snd] in *. lia.
    + constructor; [exact Hf| exact (IH Hr)].
Qed.
Lemma kmerge_sound : forall l, Forall (zf_den E) l -> Forall (zf_den E) (kmerge l).
Proof.
  intros l. unfold kmerge. assert (G : forall acc, Forall (zf_den E) acc -> Forall (zf_den E) l -> Forall (zf_den E) (fold_left (fun acc f => zadd f acc) l acc)).
  { induction l as [|f r IH]; intros acc HA HL; cbn [fold_left]; [exact HA|]. apply Forall_cons_iff in HL as [Hf Hr]. apply IH; [|exact Hr].
    unfold zadd. destruct f as [[c ts] lo hi| | | |]; try (apply Forall_app; split; [exact HA| constructor; [exact Hf| constructor]]).
    apply zins_rng_sound; [|exact HA]. cbn [zf_den] in Hf. rewrite pden_ok in Hf. cbn [fst snd] in Hf. lia. }
  intros H. apply G; [constructor| exact H].
Qed.

Lemma bdig_sound : forall allkn t c a b f, know_ok segs E M allkn -> bdig allkn t c a b = Some f ->
  branch_taken c (edenot E a) (edenot E b) = t -> zf_den E f.
Proof.
  intros allkn t c a b f HA H HB. unfold bdig in H.
  destruct (lin_nowrap allkn a && lin_nowrap allkn b)%bool eqn:C; [|discriminate].
  apply andb_prop in C as [Ca Cb].
  pose proof (lin_nowrap_sound segs E M allkn a HA Ca) as Qa. pose proof (lin_nowrap_sound segs E M allkn b HA Cb) as Qb.
  destruct c, t; try discriminate H; injection H as <-; cbn [zf_den]; rewrite pden_ok;
    rewrite ?ld_sub, ?ld_addc; rewrite ?ld_sub; rewrite <- Qa, <- Qb; cbn [branch_taken] in HB;
    unfold bv_eqb, bv_ltu in HB;
    repeat match type of HB with
      | negb _ = true => apply negb_true_iff in HB
      | negb _ = false => apply negb_false_iff in HB
      | Z.eqb _ _ = true => apply Z.eqb_eq in HB
      | Z.eqb _ _ = false => apply Z.eqb_neq in HB
      | Z.ltb _ _ = true => apply Z.ltb_lt in HB
      | Z.ltb _ _ = false => apply Z.ltb_ge in HB
      end; lia.
Qed.

Lemma pdigest_sound : forall allkn p, know_ok segs E M allkn -> scs_denot segs M E p -> Forall (zf_den E) (pdigest allkn p).
Proof.
  intros allkn p HA. induction p as [|s r IH]; intros HP; cbn [pdigest]; [constructor|].
  unfold scs_denot in HP. apply Forall_cons_iff in HP as [H1 HR]. specialize (IH HR).
  destruct s as [t c a b| | | | | |]; try exact IH.
  destruct (bdig allkn t c a b) as [f|] eqn:Hb; [|exact IH].
  constructor; [|exact IH]. exact (bdig_sound allkn t c a b f HA Hb H1).
Qed.

Lemma pleft_sound : forall allkn p, scs_denot segs M E p -> scs_denot segs M E (pleft allkn p).
Proof.
  intros allkn p HP. unfold scs_denot, pleft in *. apply Forall_forall. intros s Hs. apply filter_In in Hs as [Hs _].
  rewrite Forall_forall in HP. exact (HP s Hs).
Qed.
End Sound.

(* [comment removed for export] *)
Lemma edenot_EVar : forall E n, edenot E (EVar n) = ev E n.
Proof. reflexivity. Qed.

Ltac vp_forall H :=
  repeat match type of H with
  | Forall _ (_ :: _) => apply Forall_cons_iff in H; let X := fresh "Z" in destruct H as [X H]
  | Forall _ [] => clear H
  end.
Ltac vp_forallP H :=
  repeat match type of H with
  | Forall _ (_ :: _) => apply Forall_cons_iff in H; let X := fresh "P" in destruct H as [X H]
  | Forall _ [] => clear H
  end.

Ltac vp_digest segs E m HK HP :=
  lazymatch type of HK with know_ok _ _ _ ?kn =>
  lazymatch type of HP with scs_denot _ _ _ ?p =>
    let lk := eval vm_compute in (kmerge (kdigest kn kn)) in
    let lp := eval vm_compute in (pdigest kn p) in
    let ll := eval vm_compute in (pleft kn p) in
    let ZK := fresh "ZK" in let ZP := fresh "ZP" in let HPL := fresh "HPL" in
    assert (ZK : Forall (zf_den E) lk)
      by (replace lk with (kmerge (kdigest kn kn)) by (vm_compute; reflexivity); exact (kmerge_sound E _ (kdigest_sound segs E m kn kn HK HK)));
    assert (ZP : Forall (zf_den E) lp)
      by (replace lp with (pdigest kn p) by (vm_compute; reflexivity); exact (pdigest_sound segs E m kn p HK HP));
    assert (HPL : scs_denot segs m E ll)
      by (replace ll with (pleft kn p) by (vm_compute; reflexivity); exact (pleft_sound segs E m kn p HP));
    clear HP;
    vp_forall ZK; vp_forall ZP;
    unfold scs_denot in HPL; vp_forallP HPL
  end end;
  cbn [zf_den pden psum pterm fst snd Z.eqb Pos.eqb] in *;
  unfold uE in *; rewrite ?edenot_EVar in *.

(* [comment removed for export] *)
Ltac vp_lin segs E m HK :=
  repeat match goal with
  | |- context [bv_unsigned (edenot E ?e)] =>
      lazymatch e with EVar _ => fail | ELit _ => fail | _ => idtac end;
      rewrite (u_lin segs E m _ e HK ltac:(vm_compute; reflexivity))
  end;
  cbn [pden psum pterm fst snd Z.eqb Pos.eqb lin_of ladd lscale lscale_terms lins snorm] ;
  unfold uE; rewrite ?edenot_EVar.

End VP.
