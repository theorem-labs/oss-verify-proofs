(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame RefMemcpyLib MemSplit PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma rdn_agree : forall segs M M' n (a : word),
  (forall j, (j < n)%nat -> M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) = M' (Z_to_bv 64 (bv_unsigned a + Z.of_nat j))) ->
  rdn segs M a n = rdn segs M' a n.
Proof.
  intros segs M M' n. induction n as [|n IH]; intros a Hag; [reflexivity|].
  cbn [rdn].
  pose proof (Hag 0%nat ltac:(lia)) as H0.
  rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned in H0. rewrite H0.
  rewrite (IH (a + 1)); [reflexivity|].
  intros j Hj. rewrite w_add_1.
  pose proof (u64_range a) as Ha.
  destruct (Z_lt_le_dec (bv_unsigned a + 1) (2 ^ 64)) as [Hlt | Hge].
  - rewrite u_small by lia.
    replace (bv_unsigned a + 1 + Z.of_nat j)%Z with (bv_unsigned a + Z.of_nat (S j))%Z by lia.
    apply Hag. lia.
  - replace (Z_to_bv 64 (bv_unsigned a + 1)) with (Z_to_bv 64 0)
      by (apply bv_eq; rewrite !Z_to_bv_unsigned, !bv_wrap64_mod; replace (bv_unsigned a + 1)%Z with (2^64)%Z by lia; reflexivity).
    change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    specialize (Hag (S j) ltac:(lia)).
    replace (bv_unsigned a + Z.of_nat (S j))%Z with (2 ^ 64 + Z.of_nat j)%Z in Hag by lia.
    replace (Z_to_bv 64 (2 ^ 64 + Z.of_nat j)) with (Z_to_bv 64 (0 + Z.of_nat j)) in Hag; [exact Hag|].
    apply bv_eq. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod.
    rewrite <- (Zplus_mod_idemp_l (2 ^ 64) (Z.of_nat j)), Z_mod_same_full. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition apart_b (allkn : list kentry) (ub : expr) (uk un : Z) (b : expr) (k n : Z) : bool :=
  if expr_eqb b ub then (Z.leb (k + n) uk || Z.leb (uk + un) k)%bool
  else ranges_apart allkn ub uk un b k n.

Lemma apart_b_sound : forall segs E M allkn ub uk un b k n,
  know_ok segs E M allkn -> apart_b allkn ub uk un b k n = true ->
  ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z).
Proof.
  intros segs E M allkn ub uk un b k n HK H. unfold apart_b in H.
  destruct (expr_eqb b ub) eqn:Heq.
  - apply expr_eqb_eq in Heq. subst b. unfold estart. cbn [a_base a_off].
    apply orb_prop in H. destruct H as [H|H]; apply Z.leb_le in H; lia.
  - eapply ranges_apart_sound; [exact HK | exact H].
Qed.

(* [comment removed for export] *)
Definition kn_frame1 (allkn : list kentry) (ub : expr) (uk un : Z) (K : kentry) : list kentry :=
  match K with
  | KWord (SA b k) w _ => if apart_b allkn ub uk un b k (Z.of_nat w) then [K] else []
  | KZero (SA b k) (ELit l) =>
      if (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool then
        if apart_b allkn ub uk un b k l then [K]
        else if expr_eqb b ub then
          (if Z.ltb k uk then [KZero (SA b k) (ELit (Z.min l (uk - k)))] else [])
          ++ (if Z.ltb (uk + un) (k + l) then [KZero (SA b (Z.max k (uk + un))) (ELit (k + l - Z.max k (uk + un)))] else [])
        else []
      else []
  | KZero _ _ => []
  | KBlob (SA b k) (ELit l) _ => if (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b allkn ub uk un b k l)%bool then [K] else []
  | KBlob _ _ _ => []
  | KBlobD (SA b k) (ELit l) _ => if (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b allkn ub uk un b k l)%bool then [K] else []
  | KBlobD _ _ _ => []
  | KImg lo hi => if (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b allkn ub uk un (ELit 0) lo (hi - lo))%bool then [K] else []
  | KAlign _ _ => [K]
  | KRange _ _ _ => [K]
  | KDisj _ _ _ _ => [K]
  | KWr _ _ => [K]
  end.

Definition kn_frame (kn : list kentry) (ub : expr) (uk un : Z) : list kentry :=
  flat_map (kn_frame1 kn ub uk un) kn.

Lemma edenot_lit0 : forall E, bv_unsigned (edenot E (ELit 0)) = 0%Z.
Proof. intros. reflexivity. Qed.

Lemma know_ok_frame : forall segs E M M' kn ub uk un,
  know_ok segs E M kn -> flat E (SA ub uk) un ->
  (forall x : word,
     (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + un <= bv_unsigned x)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok segs E M' (kn_frame kn ub uk un).
Proof.
  intros segs E M M' kn ub uk un HK Hfl OUT GR.
  pose proof (flat_u E _ _ Hfl) as Hu. destruct Hfl as (F1 & F2 & F3 & F4).
  unfold know_ok, kn_frame. apply Forall_forall. intros K' HinF.
  apply in_flat_map in HinF as (K & Hin & Hb).
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  assert (APART : forall b k n, apart_b kn ub uk un b k n = true ->
            ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z)).
  { intros b k n H. eapply apart_b_sound; [exact HK | exact H]. }
  assert (BLOB : forall b k l bk (K0 : kentry),
    (K0 = KBlob (SA b k) (ELit l) bk \/ K0 = KBlobD (SA b k) (ELit l) bk) ->
    kentry_ok segs E M K0 ->
    In K' (if (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b kn ub uk un b k l)%bool then [K0] else []) ->
    kentry_ok segs E M' K').
  { intros b k l bk K0 HK0 HKK0 Hb0.
    destruct (Z.leb 0 l && Z.ltb l (2 ^ 64) && apart_b kn ub uk un b k l)%bool eqn:Hl; [|destruct Hb0].
    destruct Hb0 as [<-|[]].
    apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    assert (HH : flat E (SA b k) (elenZ E (ELit l)) /\ Z.of_nat (length (eb E bk)) = elenZ E (ELit l)
                 /\ forall i, (0 <= i < elenZ E (ELit l))%Z ->
                      M (Z_to_bv 64 (estart E (SA b k) + i)) = Some (nth (Z.to_nat i) (eb E bk) (Z_to_bv 8 0))).
    { destruct HK0 as [-> | ->]; exact HKK0. }
    destruct HH as (Hf & Hlen & Hz). rewrite El in *. destruct Hf as (G1 & G2 & G3 & G4).
    assert (HH' : flat E (SA b k) (elenZ E (ELit l)) /\ Z.of_nat (length (eb E bk)) = elenZ E (ELit l)
                  /\ forall i, (0 <= i < elenZ E (ELit l))%Z ->
                       M' (Z_to_bv 64 (estart E (SA b k) + i)) = Some (nth (Z.to_nat i) (eb E bk) (Z_to_bv 8 0))).
    { rewrite El. split; [unfold flat; lia|]. split; [exact Hlen|].
      intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
      rewrite u_small by lia. destruct (APART b k l Hap); lia. }
    destruct HK0 as [-> | ->]; exact HH'. }
  destruct K as [[b k] w v|[b k] len|[b k] len bk|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
    cbn [kn_frame1] in Hb.
  - (* [comment removed for export] *)
    destruct (apart_b kn ub uk un b k (Z.of_nat w)) eqn:Hap; [|destruct Hb].
    destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
    destruct HKK as (Hw & Hf & Hr). split; [exact Hw|]. split; [exact Hf|].
    rewrite <- Hr. apply rdn_agree. intros j Hj.
    pose proof (flat_u E _ _ Hf) as Hub. destruct Hf as (G1 & G2 & G3 & G4).
    apply OUT. rewrite u_small by lia. destruct (APART b k (Z.of_nat w) Hap); lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    destruct (Z.leb 0 l && Z.ltb l (2 ^ 64))%bool eqn:Hl; [|destruct Hb].
    apply andb_prop in Hl as [Hl0 Hl1]. apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK. destruct HKK as (Hf & Hz).
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. pose proof Hf as Hf0. destruct Hf as (G1 & G2 & G3 & G4).
    destruct (apart_b kn ub uk un b k l) eqn:Hap.
    + destruct Hb as [<-|[]]. cbn [kentry_ok]. rewrite El. split; [exact Hf0|].
      intros i Hi. rewrite OUT; [apply Hz; exact Hi|].
      rewrite u_small by lia. destruct (APART b k l Hap); lia.
    + destruct (expr_eqb b ub) eqn:Heq; [|destruct Hb].
      apply expr_eqb_eq in Heq. subst b.
      unfold estart in G1, G2, G4, OUT, Hz |- *. cbn [a_base a_off] in G1, G2, G4, OUT, Hz |- *.
      apply in_app_or in Hb. destruct Hb as [Hb|Hb].
      * destruct (Z.ltb k uk) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
        destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
        rewrite u_small by lia. split; [split; [exact G1 | split; [exact G2 | split; lia]]|].
        intros i Hi. rewrite OUT; [apply Hz; lia|]. rewrite u_small by lia. lia.
      * destruct (Z.ltb (uk + un) (k + l)) eqn:Hlt; [|destruct Hb]. apply Z.ltb_lt in Hlt.
        destruct Hb as [<-|[]]. cbn [kentry_ok]. unfold flat, elenZ, estart. cbn [a_base a_off edenot].
        rewrite u_small by lia. split; [split; [lia | split; [lia | split; lia]]|].
        intros i Hi. rewrite OUT; [|rewrite u_small by lia; lia].
        replace (bv_unsigned (edenot E ub) + Z.max k (uk + un) + i)%Z
          with (bv_unsigned (edenot E ub) + k + (Z.max k (uk + un) - k + i))%Z by lia.
        apply Hz. lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    eapply (BLOB b k l bk); [left; reflexivity | exact HKK | exact Hb].
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | | | | | |]; try (destruct Hb; fail); [|destruct Hb..].
    eapply (BLOB b k l bk); [right; reflexivity | exact HKK | exact Hb].
  - (* [comment removed for export] *)
    destruct (Z.leb 0 lo && Z.ltb lo hi && Z.leb hi (2 ^ 64) && apart_b kn ub uk un (ELit 0) lo (hi - lo))%bool eqn:Hl; [|destruct Hb].
    destruct Hb as [<-|[]].
    apply andb_prop in Hl as [Hl Hap]. apply andb_prop in Hl as [Hl Hhi]. apply andb_prop in Hl as [Hlo Hlh].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hlh. apply Z.leb_le in Hhi.
    cbn [kentry_ok] in HKK |- *. destruct HKK as (H0 & H1 & Hnone). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite OUT; [apply Hnone; exact Hi|].
    pose proof (APART (ELit 0) lo (hi - lo)%Z Hap) as AP. unfold estart in AP |- *. cbn [a_base a_off] in AP |- *.
    rewrite edenot_lit0 in AP. rewrite u_small by lia. lia.
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
  - (* [comment removed for export] *)
    destruct Hb as [<-|[]]. cbn [kentry_ok] in HKK |- *.
    destruct HKK as (Hf & Hst). split; [exact Hf|].
    intros d m Hd Hm. eapply store_ok_mono; [exact GR | apply Hst; assumption].
  - (* [comment removed for export] *) destruct Hb as [<-|[]]. exact HKK.
Qed.

(* [comment removed for export] *)
Fixpoint kn_frames (kn : list kentry) (rs : list (saddr * Z)) : list kentry :=
  match rs with
  | [] => kn
  | (SA ub uk, un) :: rest => kn_frames (kn_frame kn ub uk un) rest
  end.

Lemma know_ok_frames : forall segs E rs M M' kn,
  know_ok segs E M kn ->
  Forall (fun r => flat E (fst r) (snd r)) rs ->
  (forall x : word,
     Forall (fun r => (bv_unsigned x < estart E (fst r) \/ estart E (fst r) + snd r <= bv_unsigned x)%Z) rs ->
     M' x = M x) ->
  mem_grows M M' ->
  know_ok segs E M' (kn_frames kn rs).
Proof.
  intros segs E rs. induction rs as [|[[ub uk] un] rest IH]; intros M M' kn HK Hfl OUT GR.
  - cbn [kn_frames].
    assert (HM : M' = M) by (apply functional_extensionality; intros x; apply OUT; constructor).
    rewrite HM. exact HK.
  - cbn [kn_frames]. apply Forall_cons_iff in Hfl as [Hf Hfr]. cbn [fst snd] in Hf.
    set (Mi := fun x : word => if in_rngb x (adenot E (SA ub uk)) un then M' x else M x).
    pose proof (flat_u E _ _ Hf) as Hu.
    apply (IH Mi M').
    + apply (know_ok_frame segs E M Mi kn ub uk un HK Hf).
      * intros x Hx. subst Mi. cbv beta.
        destruct (in_rngb x (adenot E (SA ub uk)) un) eqn:Hin; [|reflexivity].
        apply in_rngb_spec in Hin. unfold in_rng in Hin. rewrite Hu in Hin. lia.
      * intros x Hx. subst Mi. cbv beta. destruct (in_rngb x (adenot E (SA ub uk)) un); [apply GR; exact Hx | exact Hx].
    + exact Hfr.
    + intros x Hx. subst Mi. cbv beta.
      destruct (in_rngb x (adenot E (SA ub uk)) un) eqn:Hin; [reflexivity|].
      apply OUT. constructor; [| exact Hx]. cbn [fst snd].
      destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA ub uk))) as [Hlt|Hge]; [left; exact Hlt | right].
      destruct (Z_lt_le_dec (bv_unsigned x) (estart E (SA ub uk) + un)) as [Hlt2|Hge2]; [| exact Hge2].
      exfalso. assert (Hc : in_rngb x (adenot E (SA ub uk)) un = true); [|rewrite Hc in Hin; discriminate].
      apply in_rngb_spec. unfold in_rng. rewrite Hu. lia.
    + intros x Hx. subst Mi. cbv beta in Hx. destruct (in_rngb x (adenot E (SA ub uk)) un); [exact Hx | apply GR; exact Hx].
Qed.

(* [comment removed for export] *)
Definition regions_denot (E : env) (rs : list (saddr * Z)) : list (word * Z) :=
  map (fun r => (adenot E (fst r), snd r)) rs.

Lemma know_ok_frame_mod : forall segs E rs M M' kn,
  know_ok segs E M kn ->
  Forall (fun r => flat E (fst r) (snd r)) rs ->
  frame_mod M M' (regions_denot E rs) ->
  know_ok segs E M' (kn_frames kn rs).
Proof.
  intros segs E rs M M' kn HK Hfl [Hout Hgr].
  apply (know_ok_frames segs E rs M M' kn HK Hfl); [| exact Hgr].
  intros x Hx. apply Hout. clear -Hx Hfl.
  induction rs as [|[a n] rest IH]; cbn [regions_denot map outside]; [exact I|].
  apply Forall_cons_iff in Hx as [H1 H2]. apply Forall_cons_iff in Hfl as [F1 F2]. cbn [fst snd] in *.
  split; [| apply IH; assumption].
  unfold in_rng. rewrite (flat_u E _ _ F1). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint entry_in_regions (a : saddr) (w : nat) (rs : list (saddr * Z)) : bool :=
  match rs with
  | [] => false
  | (SA b k, n) :: rest =>
      ((expr_eqb (a_base a) b && Z.leb k (a_off a) && Z.leb (a_off a + Z.of_nat w) (k + n))
       || entry_in_regions a w rest)%bool
  end.

Fixpoint log_in_regions (log : list sentry) (rs : list (saddr * Z)) : bool :=
  match log with
  | [] => true
  | SE a w _ :: rest => (entry_in_regions a w rs && log_in_regions rest rs)%bool
  end.

Lemma outside_regions_apart : forall E rs a w (x : word),
  Forall (fun r => flat E (fst r) (snd r)) rs ->
  entry_in_regions a w rs = true ->
  outside x (regions_denot E rs) ->
  (bv_unsigned x < estart E a \/ estart E a + Z.of_nat w <= bv_unsigned x)%Z.
Proof.
  intros E rs a w x Hfl. induction rs as [|[[b k] n] rest IH]; cbn [entry_in_regions regions_denot map outside]; intros H Hout;
    [discriminate|].
  apply Forall_cons_iff in Hfl as [F1 F2]. cbn [fst snd] in *. destruct Hout as [Hno Hrest].
  apply orb_prop in H as [H|H]; [| exact (IH F2 H Hrest)].
  apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
  apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
  unfold in_rng in Hno. rewrite (flat_u E _ _ F1) in Hno.
  destruct a as [ab ak]. cbn [a_base a_off] in *. subst ab. unfold estart in *. cbn [a_base a_off] in *. lia.
Qed.

Lemma frame_mod_mem_denot : forall E M log rs,
  log_flat E log ->
  Forall (fun r => flat E (fst r) (snd r)) rs ->
  log_in_regions log rs = true ->
  frame_mod M (mem_denot E M log) (regions_denot E rs).
Proof.
  intros E M log rs Hlf Hfl. induction log as [|[a w v] rest IH]; cbn [log_in_regions mem_denot]; intros H.
  - apply frame_mod_refl.
  - cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfa & Hlr).
    apply andb_prop in H as [H1 H2].
    eapply frame_mod_trans_same; [exact (IH Hlr H2)|].
    split.
    + intros x Hx. apply Frame.wbytes_outside.
      * rewrite length_N_to_le_bytes. unfold in_rng. rewrite (flat_u E _ _ Hfa).
        pose proof (outside_regions_apart E rs a w x Hfl H1 Hx). lia.
      * rewrite length_N_to_le_bytes. rewrite (flat_u E _ _ Hfa). destruct Hfa as (?&?&?&?). lia.
    + apply wbytes_grows.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint lz_byte (log : list sentry) (b : expr) (i : Z) : bool :=
  match log with
  | [] => false
  | SE (SA kb kk) w v :: rest =>
      if (expr_eqb kb b && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool
      then match v with ELit 0 => true | _ => false end
      else if expr_eqb kb b then lz_byte rest b i
      else false   (* [comment removed for export] *)
  end.

Fixpoint lz_cover (log : list sentry) (b : expr) (lo : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => (lz_byte log b lo && lz_cover log b (lo + 1) n')%bool
  end.

Lemma nth_Z_to_le_bytes_0 : forall w j, nth j (Z_to_le_bytes w 0) (Z_to_bv 8 0) = Z_to_bv 8 0.
Proof.
  induction w as [|w IH]; intros j; cbn [Z_to_le_bytes]; [destruct j; reflexivity|].
  destruct j as [|j]; [reflexivity|]. cbn [nth]. rewrite Z.shiftr_0_l. apply IH.
Qed.

Lemma mem_denot_lz_byte : forall E M log b i,
  log_flat E log -> lz_byte log b i = true ->
  (0 <= bv_unsigned (edenot E b) + i < 2 ^ 64)%Z ->
  mem_denot E M log (Z_to_bv 64 (bv_unsigned (edenot E b) + i)) = Some (Z_to_bv 8 0).
Proof.
  intros E M log b i. induction log as [|[[kb kk] w v] rest IH]; cbn [lz_byte mem_denot log_flat]; intros Hlf H Hi;
    [discriminate|].
  destruct Hlf as (Hw8 & Hfl & Hlr).
  pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
  destruct (expr_eqb kb b && Z.leb kk i && Z.ltb i (kk + Z.of_nat w))%bool eqn:Hc.
  - apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.ltb_lt in H3. subst kb.
    destruct v as [z| | | | | | | | | | |]; try discriminate. destruct z; try discriminate.
    rewrite wbytes_inside.
    + rewrite Hu, u_small by lia. cbn [edenot]. unfold word_to_le_bytes.
      change (bv_unsigned (Z_to_bv 64 0)) with 0%Z. rewrite nth_Z_to_le_bytes_0. reflexivity.
    + rewrite length_N_to_le_bytes, Hu. destruct Hfl as (?&?&?&?). unfold estart in *. cbn [a_base a_off] in *. lia.
    + rewrite length_N_to_le_bytes, Hu, u_small by lia. lia.
  - destruct (expr_eqb kb b) eqn:Heq; [|discriminate].
    apply expr_eqb_eq in Heq. subst kb.
    rewrite Frame.wbytes_outside.
    + apply IH; assumption.
    + rewrite length_N_to_le_bytes. unfold in_rng. rewrite Hu, u_small by lia.
      rewrite Z.leb_le in Hc |- * || idtac.
      assert (~ (kk <= i < kk + Z.of_nat w)%Z).
      { intros Hc2. rewrite (proj2 (Z.leb_le _ _)) in Hc by lia. rewrite (proj2 (Z.ltb_lt _ _)) in Hc by lia.
        cbn in Hc. discriminate. }
      lia.
    + rewrite length_N_to_le_bytes, Hu. destruct Hfl as (?&?&?&?). unfold estart in *. cbn [a_base a_off] in *. lia.
Qed.

Lemma mem_denot_lz_cover : forall E M log b lo n,
  log_flat E log -> lz_cover log b lo n = true ->
  (0 <= bv_unsigned (edenot E b) + lo)%Z -> (bv_unsigned (edenot E b) + lo + Z.of_nat n <= 2 ^ 64)%Z ->
  forall i, (lo <= i < lo + Z.of_nat n)%Z ->
    mem_denot E M log (Z_to_bv 64 (bv_unsigned (edenot E b) + i)) = Some (Z_to_bv 8 0).
Proof.
  intros E M log b lo n Hlf. revert lo. induction n as [|n IH]; intros lo Hc Hlo Hhi i Hi; [lia|].
  cbn [lz_cover] in Hc. apply andb_prop in Hc as [Hb Hr].
  destruct (Z.eq_dec i lo) as [->|Hne].
  - apply mem_denot_lz_byte; [exact Hlf | exact Hb | lia].
  - apply (IH (lo + 1)%Z); [exact Hr | lia | lia | lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KRead.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition kread (kn : list kentry) (b : expr) (k : Z) (n : nat) : option expr :=
  match know_lookup segs kn b k n false [] [] with
  | LHit v [] _ => Some v
  | _ => None
  end.

Lemma kread_sound : forall E M kn b k n v,
  know_ok segs E M kn -> kread kn b k n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
  flat E (SA b k) (Z.of_nat n) ->
  exists bs, rdn segs M (adenot E (SA b k)) n = Some bs /\ length bs = n
             /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E v.
Proof.
  intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl. unfold kread in Hr.
  pose proof (know_lookup_sound segs E M kn b k n false [] [] Hkn Hn1 Hn8) as Hs.
  destruct (know_lookup segs kn b k n false [] []) as [v' scs h|scs h|]; try discriminate.
  destruct scs; [|discriminate]. injection Hr as ->.
  destruct (Hs ltac:(constructor) Hfl) as (bs & A & B & C). exists bs. unfold extz in C. auto.
Qed.

Lemma word_to_le_bytes_of_lez : forall n bs,
  length bs = n -> (n <= 8)%nat -> word_to_le_bytes n (Z_to_bv 64 (bytes_le_to_Z bs)) = bs.
Proof.
  intros n bs Hl Hn. unfold word_to_le_bytes.
  pose proof (bytes_le_to_Z_bound bs) as Hb. rewrite Hl in Hb.
  assert (Hlt : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
  rewrite Z_to_bv_unsigned, bv_wrap64_mod, Z.mod_small by lia.
  rewrite <- Hl. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
Lemma kread_rdn : forall E M kn b k n v,
  know_ok segs E M kn -> kread kn b k n = Some v -> (1 <= n)%nat -> (n <= 8)%nat ->
  flat E (SA b k) (Z.of_nat n) ->
  rdn segs M (adenot E (SA b k)) n = Some (word_to_le_bytes n (edenot E v)).
Proof.
  intros E M kn b k n v Hkn Hr Hn1 Hn8 Hfl.
  destruct (kread_sound E M kn b k n v Hkn Hr Hn1 Hn8 Hfl) as (bs & A & B & C).
  rewrite A, <- C, word_to_le_bytes_of_lez by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma know_nth : forall E M kn i K,
  know_ok segs E M kn -> nth_error kn i = Some K -> kentry_ok segs E M K.
Proof.
  intros E M kn i K HK Hi. unfold know_ok in HK. rewrite Forall_forall in HK.
  apply HK. eapply nth_error_In. exact Hi.
Qed.

Lemma know_ok_app : forall E M k1 k2,
  know_ok segs E M k1 -> know_ok segs E M k2 -> know_ok segs E M (k1 ++ k2).
Proof. intros. unfold know_ok. apply Forall_app. auto. Qed.

Lemma know_ok_cons : forall E M K kn,
  kentry_ok segs E M K -> know_ok segs E M kn -> know_ok segs E M (K :: kn).
Proof. intros. constructor; assumption. Qed.

(* [comment removed for export] *)
Lemma kwr_intro : forall E mem (e : expr) (w : word) (off n : Z),
  edenot E e = w ->
  (0 <= bv_unsigned w + off)%Z -> (0 < n)%Z -> (bv_unsigned w + off + n <= 2 ^ 64)%Z ->
  store_ok segs mem (Z_to_bv 64 (bv_unsigned w + off)) (Z.to_nat n) = true ->
  kentry_ok segs E mem (KWr (SA e off) n).
Proof.
  intros E mem e w off n He H0 Hn Hhi Hst. cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off]. rewrite He.
  pose proof (u64_range w) as Hw.
  split; [lia|]. intros d m Hd Hm. destruct m as [|m']; [reflexivity|].
  assert (U1 : bv_unsigned (Z_to_bv 64 (bv_unsigned w + off)) = (bv_unsigned w + off)%Z) by (apply u_small; lia).
  assert (U2 : bv_unsigned (Z_to_bv 64 (bv_unsigned w + off + d)) = (bv_unsigned w + off + d)%Z) by (apply u_small; lia).
  apply store_ok_of_all; [rewrite U2; lia|]. intros x Hx. rewrite U2 in Hx.
  apply (store_ok_all segs mem (Z.to_nat n) (Z_to_bv 64 (bv_unsigned w + off)) ltac:(rewrite U1, Z2Nat.id by lia; lia) Hst).
  rewrite Z2Nat.id by lia.
  rewrite U1. lia.
Qed.

End KRead.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Ltac after_call_with HR HF HK Hkeep Hfkeep FPI' :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
   lazymatch type of HF with
   | fregs_ok _ ?sfr ?FR =>
    lazymatch type of HK with
    | know_ok ?segs _ ?M ?kn =>
      lazymatch type of Hkeep with
      | forall r, In r ?kept -> getr ?R' r = getr R r =>
        env_parts E ltac:(fun VALS EBS =>
          let NX := eval cbn in (length VALS) in
          let NX' := eval cbn in (NX + 32)%nat in
          let sr' := eval vm_compute in (sr_after_call_j sr (map ridx kept) NX) in
          let FR' := constr:(fp_regs (FPState:=FPI')) in
          let HR' := fresh "HR" in let HF' := fresh "HF" in let HK' := fresh "HK" in
          (* [comment removed for export] *)
          pose proof (regs_after_keeps VALS EBS sr R R' kept ltac:(reflexivity) HR Hkeep) as HR';
          change (sr_after_call_j sr (map ridx kept) (length VALS)) with sr' in HR';
          apply (env_app_regs (VALS ++ junk_vals R') (fjunk_vals FR') EBS sr' R' ltac:(reflexivity)) in HR';
          (* [comment removed for export] *)
          lazymatch type of Hfkeep with
          | forall r, In r ?fkept -> reg_get _ r = reg_get _ r =>
              let sfr' := eval vm_compute in (sfr_after_call_j sfr (map ridx fkept) NX') in
              pose proof (fregs_after_keeps (VALS ++ junk_vals R') EBS sfr FR FR' fkept ltac:(reflexivity)
                            (env_app_fregs VALS (junk_vals R') EBS sfr FR ltac:(reflexivity) HF) Hfkeep) as HF';
              change (sfr_after_call_j sfr (map ridx fkept) (length (VALS ++ junk_vals R'))) with sfr' in HF'
          | _ =>
              let sfr' := eval vm_compute in (sfr_vars NX') in
              pose proof (fregs_ok_vars (VALS ++ junk_vals R') FR' [] EBS) as HF';
              rewrite app_nil_r in HF';
              change (sfr_vars (length (VALS ++ junk_vals R'))) with sfr' in HF'
          end;
          (* [comment removed for export] *)
          pose proof (env_app_know segs VALS (junk_vals R') EBS M kn ltac:(reflexivity) HK) as HK';
          apply (env_app_know segs (VALS ++ junk_vals R') (fjunk_vals FR') EBS M kn ltac:(reflexivity)) in HK';
          clear HR HF HK;
          rename HR' into HR; rename HF' into HF; rename HK' into HK)
      end
    end
   end
  end.

(* [comment removed for export] *)
Tactic Notation "after_call" constr(Hkeep) constr(FPI') :=
  match goal with
  | HR : regs_ok _ _ _, HF : fregs_ok _ _ _, HK : know_ok _ _ _ _ |- _ =>
      after_call_with HR HF HK Hkeep I FPI'
  end.
Tactic Notation "after_call" constr(Hkeep) constr(Hfkeep) constr(FPI') :=
  match goal with
  | HR : regs_ok _ _ _, HF : fregs_ok _ _ _, HK : know_ok _ _ _ _ |- _ =>
      after_call_with HR HF HK Hkeep Hfkeep FPI'
  end.

(* [comment removed for export] *)
Ltac flats_auto :=
  repeat (apply Forall_cons || apply Forall_nil);
  cbn [fst snd]; sc_simpl; try lia.

Ltac know_frame HK Hfr RS :=
  lazymatch type of HK with
  | know_ok ?segs ?E ?M ?kn =>
    lazymatch type of Hfr with
    | frame_mod M ?M' ?rs =>
        let kn' := eval vm_compute in (kn_frames kn RS) in
        let H := fresh "HK" in let Hfl := fresh "Hfl" in let Heq := fresh "Hkf" in
        assert (Hfl : Forall (fun r => flat E (fst r) (snd r)) RS); [flats_auto|];
        first
          [ pose proof (know_ok_frame_mod segs E RS M M' kn HK Hfl Hfr) as H
          | let Hrs := fresh "Hrs" in
            assert (Hrs : frame_mod M M' (regions_denot E RS));
            [ let Heq2 := fresh "Hrd" in
              assert (Heq2 : regions_denot E RS = rs);
              [ cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E
              | rewrite Heq2; exact Hfr ]
            | pose proof (know_ok_frame_mod segs E RS M M' kn HK Hfl Hrs) as H; clear Hrs ] ];
        [ .. |
          assert (Heq : kn_frames kn RS = kn') by (vm_compute; reflexivity);
          rewrite Heq in H; clear Heq Hfl HK; rename H into HK ]
    end
  end.
