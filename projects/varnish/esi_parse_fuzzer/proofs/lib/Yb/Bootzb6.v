(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import PropExec AxSyioe AxSyclu Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Booteo9 Bootha0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bootocl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Boots35.

Module Bootzf8.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import PropExec AxSyioe AxSyclu Asanz3l AsanPlan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bootha0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Booteo9.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootha0.Boott1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Booteo9.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BFXH.
Import AX2. Import AX2B. Import APC. Import AP.

Ltac fe := repeat (apply functional_extensionality; intros ?).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sub_itvB_g :=
  ltac:(let t := eval cbv delta [AX2B.sub_itvB] in @AX2B.sub_itvB in
        let t1 := eval pattern (@AX2.expr_eqb) in t in
        lazymatch t1 with ?G _ => exact G end).
Definition sub_itvF := sub_itvB_g BASF.expr_eqbF.
Lemma sub_itvF_fe : sub_itvF = @AX2B.sub_itvB.
Proof. unfold sub_itvF. rewrite BASF.expr_eqbF_fe. reflexivity. Qed.
Fixpoint in_sidesF (bc : bctx) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itvF bc b2 k2 n2 c m then true else in_sidesF bc r b2 k2 n2
  end.
Lemma in_sidesF_eq : forall bc D b2 k2 n2, in_sidesF bc D b2 k2 n2 = in_sidesB bc D b2 k2 n2.
Proof.
  intros bc D b2 k2 n2. induction D as [|[c m] r IH]; [reflexivity|]. cbn [in_sidesF in_sidesB]. rewrite sub_itvF_fe, IH. reflexivity.
Qed.

(* [comment removed for export] *)
Fixpoint mk_Q (bc : bctx) (D : list (saddr * expr)) (B : expr) : list (Z * Z) :=
  match D with
  | [] => []
  | (c, m) :: rest =>
      if BASF.expr_eqbF B (a_base c) then
        match xloB bc m with
        | Some ml => (a_off c, a_off c + ml) :: mk_Q bc rest B
        | None => mk_Q bc rest B
        end
      else mk_Q bc rest B
  end.
Fixpoint q_in (Q : list (Z * Z)) (k e : Z) : bool :=
  match Q with
  | [] => false
  | (lo, hi) :: r => if (if Z.leb lo k then Z.leb e hi else false) then true else q_in r k e
  end.
Lemma mk_Q_sound : forall bc D B k n, q_in (mk_Q bc D B) k (k + n) = true -> in_sidesB bc D B k n = true.
Proof.
  intros bc D B k n. induction D as [|[c m] rest IH]; intros H; [discriminate|].
  cbn [mk_Q] in H. cbn [in_sidesB].
  destruct (sub_itvB bc B k n c m) eqn:ES; [reflexivity|].
  destruct (BASF.expr_eqbF B (a_base c)) eqn:E; [|apply IH; exact H].
  destruct (xloB bc m) as [ml|] eqn:EX; [|apply IH; exact H].
  cbn [q_in] in H. destruct (Z.leb (a_off c) k) eqn:E1; [|apply IH; exact H].
  destruct (Z.leb (k + n) (a_off c + ml)) eqn:E2; [|apply IH; exact H].
  exfalso. unfold sub_itvB in ES. rewrite BASF.expr_eqbF_eq in E. rewrite E, E1, EX, E2 in ES. cbn in ES. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition mkS1 (sp : sprep) (k1 m1 : Z) : option (Z * Z) :=
  match sp_rng sp with Some (lo1, hi1) => Some (hi1 + k1 + m1, lo1 + k1) | None => None end.
(* [comment removed for export] *)
Definition mkT (S1 : option (Z * Z)) (r2 : option (Z * Z)) : option (Z * Z) :=
  match S1, r2 with Some (A1, B1), Some (lo2, hi2) => Some (A1 - lo2, B1 - hi2) | _, _ => None end.
Definition itvT (T : option (Z * Z)) (k2 m2 : Z) : bool :=
  match T with Some (t1, t2) => if Z.leb t1 k2 then true else Z.leb (k2 + m2) t2 | None => false end.
Lemma itvT_eq : forall sp k1 m1 r2 k2 m2,
  itvT (mkT (mkS1 sp k1 m1) r2) k2 m2
  = match sp_rng sp, r2 with
    | Some (lo1, hi1), Some (lo2, hi2) => (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
    | _, _ => false
    end.
Proof.
  intros sp k1 m1 r2 k2 m2. unfold mkS1, mkT, itvT. destruct (sp_rng sp) as [[lo1 hi1]|]; [|reflexivity].
  destruct r2 as [[lo2 hi2]|]; [|reflexivity].
  destruct (Z.leb_spec (hi1 + k1 + m1 - lo2) k2), (Z.leb_spec (hi1 + k1 + m1) (lo2 + k2)); cbn [orb]; try reflexivity; try (exfalso; lia).
  destruct (Z.leb_spec (k2 + m2) (lo1 + k1 - hi2)), (Z.leb_spec (hi2 + k2 + m2) (lo1 + k1)); try reflexivity; exfalso; lia.
Qed.

Record rent : Type := RE { re_b : expr; re_t : option (Z * Z); re_q : list (Z * Z) }.
Definition rcache : Type := list rent.
Definition mk_rent (bc : bctx) (D : list (saddr * expr)) (S1 : option (Z * Z)) (B : expr) : rent :=
  RE B (mkT S1 (base_rangeB bc B)) (mk_Q bc D B).
Definition RCOK (bc : bctx) (D : list (saddr * expr)) (S1 : option (Z * Z)) (c : rcache) : Prop :=
  forall e, In e c -> e = mk_rent bc D S1 (re_b e).
Lemma RCOK_nil : forall bc D S1, RCOK bc D S1 []. Proof. intros bc D S1 e []. Qed.

(* [comment removed for export] *)
Fixpoint rc_take (c : rcache) (B : expr) : option (rent * rcache) :=
  match c with
  | [] => None
  | e :: rest =>
      if BASF.expr_eqbF B (re_b e) then Some (e, rest)
      else match rc_take rest B with
           | Some (e0, rest') => Some (e0, e :: rest')
           | None => None
           end
  end.
Lemma rc_take_spec : forall bc D S1 c B e c', RCOK bc D S1 c -> rc_take c B = Some (e, c') -> e = mk_rent bc D S1 B /\ RCOK bc D S1 c'.
Proof.
  intros bc D S1 c B. induction c as [|e1 rest IH]; intros e c' H T; [discriminate|]. cbn [rc_take] in T.
  destruct (BASF.expr_eqbF B (re_b e1)) eqn:E.
  - injection T as <- <-. apply BASF.expr_eqbF_true in E. split.
    + rewrite E. apply H. left. reflexivity.
    + intros x I. apply H. right. exact I.
  - destruct (rc_take rest B) as [[e0 rest']|] eqn:T'; [|discriminate]. injection T as <- <-.
    assert (HR : RCOK bc D S1 rest) by (intros x I; apply H; right; exact I).
    destruct (IH e0 rest' HR eq_refl) as [E1 E2]. split; [exact E1|].
    intros x [I|I]; [apply H; left; exact I|apply E2; exact I].
Qed.
(* [comment removed for export] *)
Definition rc_get (bc : bctx) (D : list (saddr * expr)) (S1 : option (Z * Z)) (c : rcache) (B : expr) : rent * rcache :=
  match B with
  | ELit _ => (RE B (mkT S1 (base_rangeB bc B)) [], c)
  | _ =>
    match c with
    | e :: rest =>
        if BASF.expr_eqbF B (re_b e) then (e, c)
        else match rc_take rest B with
             | Some (e0, rest') => (e0, e0 :: e :: rest')
             | None => let e0 := mk_rent bc D S1 B in (e0, e0 :: c)
             end
    | [] => let e0 := mk_rent bc D S1 B in (e0, [e0])
    end
  end.
(* [comment removed for export] *)
Definition rent_ok (bc : bctx) (D : list (saddr * expr)) (S1 : option (Z * Z)) (B : expr) (e : rent) : Prop :=
  re_t e = mkT S1 (base_rangeB bc B) /\ forall k n, q_in (re_q e) k (k + n) = true -> in_sidesB bc D B k n = true.
Lemma mk_rent_ok : forall bc D S1 B, rent_ok bc D S1 B (mk_rent bc D S1 B).
Proof. intros. split; [reflexivity|]. intros k n. apply mk_Q_sound. Qed.
Lemma rc_get_spec : forall bc D S1 c B, RCOK bc D S1 c ->
  rent_ok bc D S1 B (fst (rc_get bc D S1 c B)) /\ RCOK bc D S1 (snd (rc_get bc D S1 c B)).
Proof.
  intros bc D S1 c B H.
  assert (G : forall c0, RCOK bc D S1 c0 ->
     let res := match c0 with
                | e :: rest =>
                    if BASF.expr_eqbF B (re_b e) then (e, c0)
                    else match rc_take rest B with
                         | Some (e0, rest') => (e0, e0 :: e :: rest')
                         | None => let e0 := mk_rent bc D S1 B in (e0, e0 :: c0)
                         end
                | [] => let e0 := mk_rent bc D S1 B in (e0, [e0])
                end in
     rent_ok bc D S1 B (fst res) /\ RCOK bc D S1 (snd res)).
  { intros c0 H0. destruct c0 as [|e rest]; cbv zeta.
    - cbn [fst snd]. split; [apply mk_rent_ok|]. intros x [<-|[]]. reflexivity.
    - destruct (BASF.expr_eqbF B (re_b e)) eqn:E.
      + cbn [fst snd]. apply BASF.expr_eqbF_true in E. split; [|exact H0].
        rewrite (H0 e (or_introl eq_refl)), <- E. apply mk_rent_ok.
      + assert (HR : RCOK bc D S1 rest) by (intros x I; apply H0; right; exact I).
        destruct (rc_take rest B) as [[e0 rest']|] eqn:T.
        * destruct (rc_take_spec bc D S1 rest B e0 rest' HR T) as [E1 E2]. cbn [fst snd]. split; [rewrite E1; apply mk_rent_ok|].
          intros x [<-|[<-|I]].
          -- rewrite E1. reflexivity.
          -- apply H0. left. reflexivity.
          -- apply E2. exact I.
        * cbn [fst snd]. split; [apply mk_rent_ok|]. intros x [<-|I]; [reflexivity|apply H0; exact I]. }
  unfold rc_get. destruct B; try (apply G; exact H).
  cbn [fst snd]. split; [|exact H]. split; [reflexivity|]. intros k n Hq. discriminate.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ranges_apart_pC (bc : bctx) (sp : sprep) (S1 : option (Z * Z)) (c : rcache) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool * rcache :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m2 := zlit64 z2 in
      let ec := rc_get bc (sp_D sp) S1 c b2 in
      if itvT (re_t (fst ec)) k2 m2 then (true, snd ec)
      else if (if q_in (re_q (fst ec)) k2 (k2 + m2) then true else in_sidesF bc (sp_D sp) b2 k2 m2) then (true, snd ec)
      else (lin_apartB bc b1 k1 (zlit64 z1) b2 k2 m2, snd ec)
  | _, _ => (ranges_apart_pB bc sp b1 k1 n1 b2 k2 n2, c)
  end.
(* [comment removed for export] *)
Definition mkS1n (sp : sprep) (k1 : Z) (n1 : expr) : option (Z * Z) :=
  match n1 with ELit z1 => mkS1 sp k1 (zlit64 z1) | _ => None end.
Lemma ranges_apart_pC_spec : forall bc sp c b1 k1 n1 b2 k2 n2, RCOK bc (sp_D sp) (mkS1n sp k1 n1) c ->
  fst (ranges_apart_pC bc sp (mkS1n sp k1 n1) c b1 k1 n1 b2 k2 n2) = ranges_apart_pB bc sp b1 k1 n1 b2 k2 n2
  /\ RCOK bc (sp_D sp) (mkS1n sp k1 n1) (snd (ranges_apart_pC bc sp (mkS1n sp k1 n1) c b1 k1 n1 b2 k2 n2)).
Proof.
  intros bc sp c b1 k1 n1 b2 k2 n2 H. unfold ranges_apart_pC.
  destruct n1 as [z1| | | | | | |]; try (split; [reflexivity|exact H]).
  destruct n2 as [z2| | | | | | |]; try (split; [reflexivity|exact H]).
  cbv zeta. cbn [mkS1n] in *. destruct (rc_get_spec bc (sp_D sp) (mkS1 sp k1 (zlit64 z1)) c b2 H) as [[ET EQ] E2].
  destruct (rc_get bc (sp_D sp) (mkS1 sp k1 (zlit64 z1)) c b2) as [e c']. cbn [fst snd] in *.
  unfold ranges_apart_pB. rewrite ET, itvT_eq, in_sidesF_eq.
  destruct (match sp_rng sp, base_rangeB bc b2 with
            | Some (lo1, hi1), Some (lo2, hi2) =>
                (Z.leb (hi1 + k1 + zlit64 z1) (lo2 + k2) || Z.leb (hi2 + k2 + zlit64 z2) (lo1 + k1))%bool
            | _, _ => false
            end); [split; [reflexivity|exact E2]|].
  destruct (q_in (re_q e) k2 (k2 + zlit64 z2)) eqn:EQ1.
  - rewrite (EQ _ _ EQ1). split; [reflexivity|exact E2].
  - destruct (in_sidesB bc (sp_D sp) b2 k2 (zlit64 z2)); split; try reflexivity; exact E2.
Qed.

Definition kentry_apart_bpC (bc : bctx) (sp : sprep) (S1 : option (Z * Z)) (c : rcache) (ub : expr) (uk : Z) (un : expr) (K : kentry) : bool * rcache :=
  match K with
  | KWord (SA b k) w _ => if Nat.leb w 8 then ranges_apart_pC bc sp S1 c ub uk un b k (ELit (Z.of_nat w)) else (false, c)
  | KZero (SA b k) l => ranges_apart_pC bc sp S1 c ub uk un b k l
  | KBlob (SA b k) l _ => ranges_apart_pC bc sp S1 c ub uk un b k l
  | KImg lo hi => if Z.leb 0 lo then if Z.leb lo hi then if Z.ltb (hi - lo) two64 then ranges_apart_pC bc sp S1 c ub uk un (ELit 0) lo (ELit (hi - lo)) else (false, c) else (false, c) else (false, c)
  | KAlign _ _ => (true, c)
  | KRange _ _ _ => (true, c)
  | KDisj _ _ _ _ => (true, c)
  | KWr (SA b k) n => ranges_apart_pC bc sp S1 c ub uk un b k n
  | KFill (SA b k) l _ => ranges_apart_pC bc sp S1 c ub uk un b k l
  | KUnk (SA b k) l => ranges_apart_pC bc sp S1 c ub uk un b k l
  end.
Lemma kentry_apart_bpC_spec : forall bc sp c ub uk un K, RCOK bc (sp_D sp) (mkS1n sp uk un) c ->
  fst (kentry_apart_bpC bc sp (mkS1n sp uk un) c ub uk un K) = kentry_apart_bpB bc sp ub uk un K
  /\ RCOK bc (sp_D sp) (mkS1n sp uk un) (snd (kentry_apart_bpC bc sp (mkS1n sp uk un) c ub uk un K)).
Proof.
  intros bc sp c ub uk un K H.
  destruct K as [[b k] w v|[b k] l|[b k] l bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2|[b k] l cc|[b k] l];
    cbn [kentry_apart_bpC kentry_apart_bpB]; try (apply ranges_apart_pC_spec; exact H); try (split; [reflexivity|exact H]).
  - destruct (Nat.leb w 8); cbn [andb]; [apply ranges_apart_pC_spec; exact H|split; [reflexivity|exact H]].
  - destruct (Z.leb 0 lo); cbn [andb]; [|split; [reflexivity|exact H]].
    destruct (Z.leb lo hi); cbn [andb]; [|split; [reflexivity|exact H]].
    destruct (Z.ltb (hi - lo) two64); cbn [andb]; [apply ranges_apart_pC_spec; exact H|split; [reflexivity|exact H]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint havoc_goC (bc : bctx) (sp : sprep) (S1 : option (Z * Z)) (ub : expr) (uk : Z) (un : expr) (k : list kentry) (c : rcache) : list kentry :=
  match k with
  | [] => []
  | K :: rest =>
      if kwr_b K then K :: havoc_goC bc sp S1 ub uk un rest c
      else
        let vc := kentry_apart_bpC bc sp S1 c ub uk un K in
        if fst vc then K :: havoc_goC bc sp S1 ub uk un rest (snd vc)
        else (match K with
              | KZero (SA kb kk) len => kzero_cutB bc ub uk un kb kk len
              | KFill (SA kb kk) len cc => kfill_cutB bc cc ub uk un kb kk len
              | KUnk (SA kb kk) len => kunk_cutB bc ub uk un kb kk len
              | _ => []
              end) ++ havoc_goC bc sp S1 ub uk un rest (snd vc)
  end.
Lemma havoc_goC_eq : forall bc sp ub uk un k c, RCOK bc (sp_D sp) (mkS1n sp uk un) c ->
  havoc_goC bc sp (mkS1n sp uk un) ub uk un k c = List.flat_map (havoc1pB bc sp ub uk un) k.
Proof.
  intros bc sp ub uk un k. induction k as [|K rest IH]; intros c H; [reflexivity|].
  cbn [havoc_goC flat_map]. unfold havoc1pB at 1.
  destruct (kwr_b K) eqn:EW; cbn [orb].
  - cbn [app]. rewrite (IH c H). reflexivity.
  - destruct (kentry_apart_bpC_spec bc sp c ub uk un K H) as [E1 E2].
    destruct (kentry_apart_bpC bc sp (mkS1n sp uk un) c ub uk un K) as [v c']. cbn [fst snd] in *. subst v.
    destruct (kentry_apart_bpB bc sp ub uk un K); rewrite (IH c' E2); reflexivity.
Qed.

Definition kn_havocB_f (bc : bctx) (ub : expr) (uk : Z) (un : expr) : list kentry :=
  let sp := mk_sprepB bc ub uk un in
  havoc_goC bc sp (mkS1n sp uk un) ub uk un (bc_fk bc) [].
Lemma kn_havocB_f_eq : forall bc ub uk un, kn_havocB_f bc ub uk un = kn_havocB bc ub uk un.
Proof. intros. unfold kn_havocB_f, kn_havocB. cbv zeta. apply havoc_goC_eq. apply RCOK_nil. Qed.

Definition kn_havocM_f (k : list kentry) := kn_havocB_f (BLKF.mkbc_m k).
Lemma kn_havocM_f_fe : kn_havocM_f = @APC.kn_havocM.
Proof. fe. unfold kn_havocM_f, kn_havocM. rewrite BLKF.mkbc_m_eq. apply kn_havocB_f_eq. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma fresh_ok_f_fe : BLKF.fresh_ok_f = @APC.fresh_ok.
Proof. fe. apply BLKF.fresh_ok_f_eq. Qed.
Lemma kn_vars_ltF_fe : BLKF.kn_vars_ltF = @APC.kn_vars_lt.
Proof. fe. apply BLKF.kn_vars_ltF_eq. Qed.
Lemma expr_vars_ltF_fe : BLKF.expr_vars_ltF = @APC.expr_vars_lt.
Proof. fe. apply BLKF.expr_vars_ltF_eq. Qed.

Definition after_call_g :=
  ltac:(let t := eval cbv delta [APC.after_call] in @APC.after_call in
        let t1 := eval pattern (@APC.fresh_ok), (@APC.kn_vars_lt), (@APC.expr_vars_lt) in t in
        lazymatch t1 with ?G _ _ _ => exact G end).
Definition after_call_f := after_call_g BLKF.fresh_ok_f BLKF.kn_vars_ltF BLKF.expr_vars_ltF.
Lemma after_call_f_fe : after_call_f = @APC.after_call.
Proof. unfold after_call_f. rewrite fresh_ok_f_fe, kn_vars_ltF_fe, expr_vars_ltF_fe. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mkbc_m_fe : BLKF.mkbc_m = @AX2B.mkbc.
Proof. fe. apply BLKF.mkbc_m_eq. Qed.

Definition summary_fill_g :=
  ltac:(let t := eval cbv delta [APC.summary_fill] in @APC.summary_fill in
        let t1 := eval pattern (@AX2B.mkbc), (@APC.kn_havocM), (@APC.after_call) in t in
        lazymatch t1 with ?G _ _ _ => exact G end).
Definition summary_fill_f := summary_fill_g BLKF.mkbc_m kn_havocM_f after_call_f.
Lemma summary_fill_f_fe : summary_fill_f = @APC.summary_fill.
Proof. unfold summary_fill_f. rewrite mkbc_m_fe, kn_havocM_f_fe, after_call_f_fe. reflexivity. Qed.

Definition after_call2_g :=
  ltac:(let t := eval cbv delta [APC.after_call2] in @APC.after_call2 in
        let t1 := eval pattern (@APC.fresh_ok), (@APC.kn_vars_lt), (@APC.expr_vars_lt) in t in
        lazymatch t1 with ?G _ _ _ => exact G end).
Definition after_call2_f := after_call2_g BLKF.fresh_ok_f BLKF.kn_vars_ltF BLKF.expr_vars_ltF.
Lemma after_call2_f_fe : after_call2_f = @APC.after_call2.
Proof. unfold after_call2_f. rewrite fresh_ok_f_fe, kn_vars_ltF_fe, expr_vars_ltF_fe. reflexivity. Qed.

(* [comment removed for export] *)
Definition summary_copy_g :=
  ltac:(let t := eval cbv delta [APC.summary_copy] in @APC.summary_copy in
        let t1 := eval pattern (@AX2B.mkbc), (@APC.kn_havocM), (@APC.after_call), (@APC.after_call2) in t in
        lazymatch t1 with ?G _ _ _ _ => exact G end).
Definition summary_copy_f := summary_copy_g BLKF.mkbc_m kn_havocM_f after_call_f after_call2_f.
Lemma summary_copy_f_fe : summary_copy_f = @APC.summary_copy.
Proof. unfold summary_copy_f. rewrite mkbc_m_fe, kn_havocM_f_fe, after_call_f_fe, after_call2_f_fe. reflexivity. Qed.

Definition node_x_g :=
  ltac:(let t := eval cbv delta [AP.node_x] in @AP.node_x in
        let t1 := eval pattern (@APC.summary_fill), (@APC.summary_copy) in t in
        lazymatch t1 with ?G _ _ => exact G end).
Definition node_x_f := node_x_g summary_fill_f summary_copy_f.
Lemma node_x_f_fe : node_x_f = @AP.node_x.
Proof. unfold node_x_f. rewrite summary_fill_f_fe, summary_copy_f_fe. reflexivity. Qed.
End BFXH.
End Bootzf8.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Bootocl.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Booteo9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootha0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootocl.Bootbrx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Boots35 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootzb6.Bootzf8 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb.Bootocl.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module BFXC.
Import AX2. Import APC. Import AP.

Ltac fe := repeat (apply functional_extensionality; intros ?).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kn_grant_filter_f (A : atable) (k : list kentry) (ms : list amap) : list kentry :=
  kn_grant_filterB A (BLKF.mkbc_m k) ms.
Lemma kn_grant_filter_f_eq : kn_grant_filter_f = @APC.kn_grant_filter.
Proof. fe. unfold kn_grant_filter_f. rewrite BLKF.mkbc_m_eq, APC.kn_grant_filterB_eqf. reflexivity. Qed.

Definition mmap_null_g :=
  ltac:(let t := eval cbv delta [APC.mmap_null] in @APC.mmap_null in
        let t1 := eval pattern (@APC.kn_grant_filter) in t in
        lazymatch t1 with ?G _ => exact G end).
Definition mmap_null_f := mmap_null_g kn_grant_filter_f.
Lemma mmap_null_f_eq : mmap_null_f = @APC.mmap_null.
Proof. unfold mmap_null_f. rewrite kn_grant_filter_f_eq. reflexivity. Qed.

Definition mmap_fixed_grant_g :=
  ltac:(let t := eval cbv delta [APC.mmap_fixed_grant] in @APC.mmap_fixed_grant in
        let t1 := eval pattern (@APC.kn_grant_filter) in t in
        lazymatch t1 with ?G _ => exact G end).
Definition mmap_fixed_grant_f := mmap_fixed_grant_g kn_grant_filter_f.
Lemma mmap_fixed_grant_f_eq : mmap_fixed_grant_f = @APC.mmap_fixed_grant.
Proof. unfold mmap_fixed_grant_f. rewrite kn_grant_filter_f_eq. reflexivity. Qed.

Definition mmap_fixed_free_g :=
  ltac:(let t := eval cbv delta [APC.mmap_fixed_free] in @APC.mmap_fixed_free in
        let t1 := eval pattern (@APC.mmap_fixed_grant) in t in
        lazymatch t1 with ?G _ => exact G end).
Definition mmap_fixed_free_f := mmap_fixed_free_g mmap_fixed_grant_f.
Lemma mmap_fixed_free_f_eq : mmap_fixed_free_f = @APC.mmap_fixed_free.
Proof. unfold mmap_fixed_free_f. rewrite mmap_fixed_grant_f_eq. reflexivity. Qed.

Definition node_mmap2_g :=
  ltac:(let t := eval cbv delta [APC.node_mmap2] in @APC.node_mmap2 in
        let t1 := eval pattern (@APC.mmap_null), (@APC.mmap_fixed_free) in t in
        lazymatch t1 with ?G _ _ => exact G end).
Definition node_mmap2_f := node_mmap2_g mmap_null_f mmap_fixed_free_f.
Lemma node_mmap2_f_eq : node_mmap2_f = @APC.node_mmap2.
Proof. unfold node_mmap2_f. rewrite mmap_null_f_eq, mmap_fixed_free_f_eq. reflexivity. Qed.

Definition node_brk2_g :=
  ltac:(let t := eval cbv delta [APC.node_brk2] in @APC.node_brk2 in
        let t1 := eval pattern (@APC.kn_grant_filter) in t in
        lazymatch t1 with ?G _ => exact G end).
Definition node_brk2_f := node_brk2_g kn_grant_filter_f.
Lemma node_brk2_f_eq : node_brk2_f = @APC.node_brk2.
Proof. unfold node_brk2_f. rewrite kn_grant_filter_f_eq. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma run_block_gc_f_fe : EXF.run_block_gc_f = @APC.run_block_gc.
Proof. fe. apply EXF.run_block_gc_f_eq. Qed.
Lemma run_block_gc_f2_fe : CAR2.run_block_gc_f2 = @APC.run_block_gc.
Proof. rewrite CAR2.run_block_gc_f2_fe. exact run_block_gc_f_fe. Qed.
(* [comment removed for export] *)
Lemma run_block_gc_f3_fe : CAR2.run_block_gc_f3 = @APC.run_block_gc.
Proof. rewrite CAR2.run_block_gc_f3_fe. exact run_block_gc_f_fe. Qed.

Definition check_g :=
  ltac:(let t := eval cbv delta [AP.check] in @AP.check in
        let t1 := eval pattern (@APC.run_block_gc), (@APC.node_mmap2), (@APC.node_brk2), (@APC.entails), (@APC.entails_h), (@AP.node_x) in t in
        lazymatch t1 with ?G _ _ _ _ _ _ => exact G end).
Lemma check_g_ref : check_g (@APC.run_block_gc) (@APC.node_mmap2) (@APC.node_brk2) (@APC.entails) (@APC.entails_h) (@AP.node_x) = @AP.check.
Proof. reflexivity. Qed.

Definition check_f := check_g CAR2.run_block_gc_f3 node_mmap2_f node_brk2_f BFXE.entails_f BFXE.entails_h_f BFXH.node_x_f.

Lemma check_f_fe : check_f = @AP.check.
Proof.
  unfold check_f. rewrite run_block_gc_f3_fe, node_mmap2_f_eq, node_brk2_f_eq, BFXE.entails_f_fe, BFXE.entails_h_f_fe, BFXH.node_x_f_fe.
  apply check_g_ref.
Qed.

Theorem check_f_eq : forall segs IT A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p,
  check_f segs IT A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p = check segs IT A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p.
Proof. intros. rewrite check_f_fe. reflexivity. Qed.
(* [comment removed for export] *)
Theorem check_f_it_eq : forall segs rs A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p,
  check_f segs (BFXI.mk_itab_ranges_f segs rs) A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p
  = check segs (APC.mk_itab_ranges segs rs) A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p.
Proof. intros. rewrite check_f_fe, BFXI.mk_itab_ranges_f_fe. reflexivity. Qed.
End BFXC.

(* [comment removed for export] *)
Ltac cert_f_plain :=
  lazymatch goal with
  | |- @eq ?T (AP.check ?segs ?IT ?A ?nx0 ?LIMIT ?XN ?XE ?XB ?HS ?KC ?bfuel ?fuel ?lc ?cs ?p) ?rhs =>
      refine (@eq_trans T (AP.check segs IT A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p)
                          (BFXC.check_f segs IT A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p) rhs
                          (@eq_sym T _ _ (BFXC.check_f_eq segs IT A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p)) _)
  end.
Ltac cert_f_it :=
  lazymatch goal with
  | |- @eq ?T (AP.check ?segs ?IT ?A ?nx0 ?LIMIT ?XN ?XE ?XB ?HS ?KC ?bfuel ?fuel ?lc ?cs ?p) ?rhs =>
      let itb := eval cbv delta [IT] in IT in
      lazymatch itb with
      | APC.mk_itab_ranges segs ?rs =>
          change IT with (APC.mk_itab_ranges segs rs);
          refine (@eq_trans T (AP.check segs (APC.mk_itab_ranges segs rs) A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p)
                              (BFXC.check_f segs (BFXI.mk_itab_ranges_f segs rs) A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p) rhs
                              (@eq_sym T _ _ (BFXC.check_f_it_eq segs rs A nx0 LIMIT XN XE XB HS KC bfuel fuel lc cs p)) _)
      end
  end.
Ltac cert_f := first [ cert_f_it | cert_f_plain ].
