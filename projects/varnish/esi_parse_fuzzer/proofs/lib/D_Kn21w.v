(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StepTac StoreOk MemSplit SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition frange : Type := (expr * Z * Z)%type.

Definition apart_all (allkn : list kentry) (rs : list frange) (b : expr) (k n : Z) : bool :=
  forallb (fun r : frange => match r with (ub, uk, un) => apart_b allkn ub uk un b k n end) rs.

Definition kn_keep1 (allkn : list kentry) (rs : list frange) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => apart_all allkn rs b k (Z.of_nat w)
  | KZero (SA b k) (ELit l) => ((0 <=? l) && (l <? 2 ^ 64) && apart_all allkn rs b k l)%Z%bool
  | KZero _ _ => false
  | KBlob (SA b k) (ELit l) _ => ((0 <=? l) && (l <? 2 ^ 64) && apart_all allkn rs b k l)%Z%bool
  | KBlob _ _ _ => false
  | KImg lo hi => ((0 <=? lo) && (lo <? hi) && (hi <=? 2 ^ 64) && apart_all allkn rs (ELit 0) lo (hi - lo))%Z%bool
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KWr (SA b k) n => ((0 <=? n) && apart_all allkn rs b k n)%Z%bool
  | KDisj _ _ _ _ => true
  end.

Definition kn_keep (kn : list kentry) (rs : list frange) : list kentry :=
  List.filter (kn_keep1 kn rs) kn.

(* [comment removed for export] *)
Definition outside_all (E : env) (rs : list frange) (x : word) : Prop :=
  forall ub uk un, In (ub, uk, un) rs ->
    (bv_unsigned x < estart E (SA ub uk) \/ estart E (SA ub uk) + un <= bv_unsigned x)%Z.

Lemma apart_all_sound : forall segs E M allkn rs b k n,
  know_ok segs E M allkn -> apart_all allkn rs b k n = true ->
  forall ub uk un, In (ub, uk, un) rs ->
    ((estart E (SA ub uk) + un <= estart E (SA b k))%Z \/ (estart E (SA b k) + n <= estart E (SA ub uk))%Z).
Proof.
  intros segs E M allkn rs b k n HK H ub uk un Hin.
  unfold apart_all in H. pose proof (proj1 (forallb_forall _ _) H (ub, uk, un) Hin) as H2. cbn in H2.
  clear H. rename H2 into H.
  eapply apart_b_sound; [exact HK | exact H].
Qed.

(* [comment removed for export] *)
Lemma footprint_outside : forall segs E M allkn rs b k n (x : word),
  know_ok segs E M allkn -> apart_all allkn rs b k n = true ->
  (estart E (SA b k) <= bv_unsigned x < estart E (SA b k) + n)%Z ->
  outside_all E rs x.
Proof.
  intros segs E M allkn rs b k n x HK H Hx ub uk un Hin.
  destruct (apart_all_sound segs E M allkn rs b k n HK H ub uk un Hin); lia.
Qed.

Section StoreOkAgree.
  Variable segs : list Segment.

  Lemma wview_agree : forall M M' (a : word), M' a = M a -> wview segs M' a = wview segs M a.
  Proof. intros M M' a H. unfold wview. rewrite H. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma store_ok_agree : forall n M M' (a : word),
    (forall j, (j < n)%nat -> M' (a + nat_to_word j) = M (a + nat_to_word j)) ->
    RiscvSemantics.store_ok segs M' a n = RiscvSemantics.store_ok segs M a n.
  Proof.
    induction n as [|n IH]; intros M M' a H; [reflexivity|].
    cbn [RiscvSemantics.store_ok].
    rewrite (wview_agree M M' a) by (pose proof (H 0%nat ltac:(lia)) as H0; rewrite word_add_nat_0 in H0; exact H0).
    destruct (wview segs M a); [|reflexivity].
    apply IH. intros j Hj.
    replace (a + 1 + nat_to_word j) with (a + nat_to_word (S j)); [apply H; lia|].
    rewrite word1_nat, nat_to_word_add_merge. reflexivity.
  Qed.
End StoreOkAgree.

(* [comment removed for export] *)
Lemma know_ok_keep : forall segs E M M' kn rs,
  know_ok segs E M kn ->
  Forall (fun r : frange => match r with (ub, uk, un) => flat E (SA ub uk) un end) rs ->
  (forall x : word, outside_all E rs x -> M' x = M x) ->
  know_ok segs E M' (kn_keep kn rs).
Proof.
  intros segs E M M' kn rs HK Hfl OUT.
  unfold know_ok, kn_keep. apply Forall_forall. intros K HinF.
  apply filter_In in HinF as [Hin Hb].
  pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  assert (OUTF : forall b k n (x : word), apart_all kn rs b k n = true ->
            (estart E (SA b k) <= bv_unsigned x < estart E (SA b k) + n)%Z -> M' x = M x).
  { intros b k n x H Hx. apply OUT. eapply footprint_outside; eassumption. }
  destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
    cbn [kn_keep1] in Hb.
  - (* [comment removed for export] *)
    cbn [kentry_ok] in HKK |- *.
    (first [ dand3 HKK as Hw Hf Hr | destruct HKK as (Hw & Hf & Hr) ]). split; [exact Hw|]. split; [exact Hf|].
    rewrite <- Hr. symmetry. apply rdn_agree. intros j Hj. symmetry.
    pose proof (flat_u E _ _ Hf) as Hub. (first [ dand4 Hf as G1 G2 G3 G4 | destruct Hf as (G1 & G2 & G3 & G4) ]).
    apply (OUTF b k (Z.of_nat w)); [exact Hb|]. rewrite u_small by lia. unfold estart in *. cbn [a_base a_off] in *. lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try discriminate Hb.
    apply andb_prop in Hb as [Hl Hap]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hz).
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. split; [exact Hf|].
    pose proof (flat_u E _ _ Hf) as Hub. (first [ dand4 Hf as G1 G2 G3 G4 | destruct Hf as (G1 & G2 & G3 & G4) ]).
    intros i Hi. rewrite (OUTF b k l); [apply Hz; exact Hi | exact Hap |].
    rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct len as [l| | | | | | |]; try discriminate Hb.
    apply andb_prop in Hb as [Hl Hap]. apply andb_prop in Hl as [Hl0 Hl1].
    apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK |- *. (first [ dand3 HKK as Hf Hlen Hz | destruct HKK as (Hf & Hlen & Hz) ]).
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
    rewrite El in *. split; [exact Hf|]. split; [exact Hlen|].
    pose proof (flat_u E _ _ Hf) as Hub. (first [ dand4 Hf as G1 G2 G3 G4 | destruct Hf as (G1 & G2 & G3 & G4) ]).
    intros i Hi. rewrite (OUTF b k l); [apply Hz; exact Hi | exact Hap |].
    rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    apply andb_prop in Hb as [Hl Hap]. apply andb_prop in Hl as [Hl Hhi]. apply andb_prop in Hl as [Hlo Hlh].
    apply Z.leb_le in Hlo. apply Z.ltb_lt in Hlh. apply Z.leb_le in Hhi.
    cbn [kentry_ok] in HKK |- *. (first [ dand3 HKK as H0 H1 Hnone | destruct HKK as (H0 & H1 & Hnone) ]). split; [exact H0|]. split; [exact H1|].
    intros i Hi. rewrite (OUTF (ELit 0) lo (hi - lo)%Z); [apply Hnone; exact Hi | exact Hap |].
    unfold estart. cbn [a_base a_off]. rewrite edenot_lit0. rewrite u_small by lia. lia.
  - (* [comment removed for export] *) exact HKK.
  - (* [comment removed for export] *) exact HKK.
  - (* [comment removed for export] *)
    apply andb_prop in Hb as [Hn Hap]. apply Z.leb_le in Hn.
    cbn [kentry_ok] in HKK |- *.
    destruct HKK as (Hf & Hst). split; [exact Hf|].
    pose proof (flat_u E _ _ Hf) as Hub. (first [ dand4 Hf as G1 G2 G3 G4 | destruct Hf as (G1 & G2 & G3 & G4) ]).
    intros d m Hd Hm. rewrite (store_ok_agree segs m M M'); [apply Hst; assumption|].
    intros j Hj. rewrite word_add_nat. apply (OUTF b k n); [exact Hap|].
    rewrite (u_small (estart E (SA b k) + d)) by lia. rewrite u_small by lia. lia.
  - (* [comment removed for export] *) exact HKK.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma kimg_sub : forall segs E M lo hi lo' hi',
  kentry_ok segs E M (KImg lo hi) -> (lo <= lo')%Z -> (hi' <= hi)%Z ->
  kentry_ok segs E M (KImg lo' hi').
Proof.
  (intros segs E M lo hi lo' hi'; (first [ intro dR_9; dand3 dR_9 as H0 H1 Hn | intros (H0 & H1 & Hn) ]); intros Hlo Hhi). cbn [kentry_ok].
  split; [lia|]. split; [lia|]. intros i Hi. apply Hn. lia.
Qed.

Lemma know_ok_app : forall segs E M kn1 kn2,
  know_ok segs E M kn1 -> know_ok segs E M kn2 -> know_ok segs E M (kn1 ++ kn2).
Proof. intros. unfold know_ok in *. apply Forall_app. split; assumption. Qed.

Lemma know_ok_In : forall segs E M kn K, know_ok segs E M kn -> In K kn -> kentry_ok segs E M K.
Proof. intros segs E M kn K HK Hin. exact (proj1 (Forall_forall _ _) HK K Hin). Qed.

(* [comment removed for export] *)
Definition kimg_pieces (pieces : list (Z * Z)) : list kentry := map (fun p => KImg (fst p) (snd p)) pieces.

Lemma know_ok_kimg_pieces : forall segs E M kn lo hi pieces,
  know_ok segs E M kn -> In (KImg lo hi) kn ->
  Forall (fun p => (lo <= fst p)%Z /\ (snd p <= hi)%Z) pieces ->
  know_ok segs E M (kimg_pieces pieces).
Proof.
  intros segs E M kn lo hi pieces HK Hin HP. unfold know_ok, kimg_pieces.
  apply Forall_map. eapply Forall_impl; [|exact HP].
  intros [a b] [Ha Hb]. cbn [fst snd] in *. eapply kimg_sub; [eapply know_ok_In; eassumption | exact Ha | exact Hb].
Qed.

(* [comment removed for export] *)
Section StoreOkMonoLocal.
  Variable segs : list Segment.
  Lemma wview_dom : forall M M' (a : word),
    (M a <> None -> M' a <> None) -> wview segs M a <> None -> wview segs M' a <> None.
  Proof.
    intros M M' a H Hw. unfold wview in *.
    destruct (M a) as [b|] eqn:Ha.
    - destruct (M' a) as [b'|] eqn:Ha'; [discriminate|]. exfalso. apply H; congruence.
    - destruct (M' a) as [b'|]; [discriminate|]. exact Hw.
  Qed.
  Lemma store_ok_mono_local : forall n M M' (a : word),
    (forall j, (j < n)%nat -> M (a + nat_to_word j) <> None -> M' (a + nat_to_word j) <> None) ->
    RiscvSemantics.store_ok segs M a n = true -> RiscvSemantics.store_ok segs M' a n = true.
  Proof.
    induction n as [|n IH]; intros M M' a H Hs; [reflexivity|].
    cbn [RiscvSemantics.store_ok] in *.
    destruct (wview segs M a) as [b|] eqn:Hv; [|discriminate].
    assert (Hw' : wview segs M' a <> None).
    { apply (wview_dom M M' a); [|rewrite Hv; discriminate].
      pose proof (H 0%nat ltac:(lia)) as H0. rewrite word_add_nat_0 in H0. exact H0. }
    destruct (wview segs M' a) as [b'|]; [|exfalso; apply Hw'; reflexivity].
    apply (IH M M'); [|exact Hs]. intros j Hj.
    replace (a + 1 + nat_to_word j) with (a + nat_to_word (S j)); [apply H; lia|].
    rewrite word1_nat, nat_to_word_add_merge. reflexivity.
  Qed.
End StoreOkMonoLocal.

Definition kn_wr_keep1 (allkn : list kentry) (vict : list frange) (K : kentry) : bool :=
  match K with
  | KWr (SA b k) n => ((0 <=? n)%Z && apart_all allkn vict b k n)%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition kn_keep2 (kn : list kentry) (rs vict : list frange) : list kentry :=
  kn_keep kn rs ++ List.filter (kn_wr_keep1 kn vict) kn.

Lemma know_ok_keep2 : forall segs E M M' kn rs vict,
  know_ok segs E M kn ->
  Forall (fun r : frange => match r with (ub, uk, un) => flat E (SA ub uk) un end) rs ->
  (forall x : word, outside_all E rs x -> M' x = M x) ->
  (forall x : word, outside_all E vict x -> M x <> None -> M' x <> None) ->
  know_ok segs E M' (kn_keep2 kn rs vict).
Proof.
  intros segs E M M' kn rs vict HK Hfl OUT DOM. unfold kn_keep2. apply know_ok_app.
  - eapply know_ok_keep; eassumption.
  - unfold know_ok. apply Forall_forall. intros K HinF.
    apply filter_In in HinF as [Hin Hb].
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
    destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
      cbn [kn_wr_keep1] in Hb; try discriminate Hb.
    apply andb_prop in Hb as [Hn Hap]. apply Z.leb_le in Hn.
    cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hst). split; [exact Hf|].
    pose proof (flat_u E _ _ Hf) as Hub. (first [ dand4 Hf as G1 G2 G3 G4 | destruct Hf as (G1 & G2 & G3 & G4) ]).
    intros d m Hd Hm. apply (store_ok_mono_local segs m M M'); [|apply Hst; assumption].
    intros j Hj. apply DOM. rewrite word_add_nat.
    eapply footprint_outside; [exact HK | exact Hap |].
    rewrite (u_small (estart E (SA b k) + d)) by lia. rewrite u_small by lia. lia.
Qed.
