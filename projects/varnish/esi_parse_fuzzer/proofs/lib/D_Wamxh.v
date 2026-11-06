(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require CatSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require WallSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require StoreOk Frame SymExec SymExec2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymAux.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.CatSim OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymAux.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Import SX2. Import SX2S.

Fixpoint log_w18 (log : list sentry) : bool :=
  match log with
  | [] => true
  | SE _ w _ :: r => (Nat.leb 1 w && Nat.leb w 8 && log_w18 r)%bool
  end.

Lemma entry_covered_flat : forall E rs a w,
  entry_covered rs a w = true -> regions_flat E rs -> (1 <= w)%nat -> flat E a (Z.of_nat w).
Proof.
  intros E rs a w. induction rs as [|[[rb rk] n] rest IH]; cbn [entry_covered]; intros Hc Hrf Hw; [discriminate|].
  apply orb_prop in Hc as [Hc|Hc].
  - apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
    apply expr_eqb_eq in H1. apply Z.leb_le in H2. apply Z.leb_le in H3.
    pose proof (Hrf (SA rb rk, n) ltac:(left; reflexivity)) as HF. cbn [fst snd] in HF.
    destruct a as [b k]. cbn [a_base a_off] in *. subst rb.
    unfold flat, estart in *. cbn [a_base a_off] in *. lia.
  - apply IH; [exact Hc| |exact Hw]. intros r Hr. apply Hrf. right. exact Hr.
Qed.

Lemma log_flat_of_covered : forall E rs log,
  log_covered rs log = true -> log_w18 log = true -> regions_flat E rs -> log_flat E log.
Proof.
  intros E rs log. induction log as [|[a w v] rest IH]; cbn [log_covered log_w18 log_flat]; intros Hc Hw Hrf; [exact I|].
  apply andb_prop in Hc as [H1 H2]. apply andb_prop in Hw as [Hw Hw3]. apply andb_prop in Hw as [Hw1 Hw2].
  apply Nat.leb_le in Hw1. apply Nat.leb_le in Hw2.
  split; [exact Hw2|]. split; [eapply entry_covered_flat; eassumption|]. apply IH; assumption.
Qed.

Lemma mem_denot_frame_mod : forall E M rs log,
  log_covered rs log = true -> log_w18 log = true -> regions_flat E rs ->
  frame_mod M (mem_denot E M log) (map (rdenot E) rs).
Proof.
  intros E M rs log Hc Hw Hrf. apply log_covered_frame; [exact Hc| exact Hrf| eapply log_flat_of_covered; eassumption].
Qed.

Lemma mem_denot_frame : forall E M rs log (x : word),
  log_covered rs log = true -> log_w18 log = true -> regions_flat E rs ->
  outside x (map (rdenot E) rs) -> mem_denot E M log x = M x.
Proof.
  intros E M rs log x Hc Hw Hrf Hout. exact (proj1 (mem_denot_frame_mod E M rs log Hc Hw Hrf) x Hout).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition kentry_eqb (K K' : kentry) : bool :=
  match K, K' with
  | KWord a w v, KWord a' w' v' => saddr_eqb a a' && Nat.eqb w w' && expr_eqb v v'
  | KZero a n, KZero a' n' => saddr_eqb a a' && expr_eqb n n'
  | KBlob a n k, KBlob a' n' k' => saddr_eqb a a' && expr_eqb n n' && Nat.eqb k k'
  | KImg l h, KImg l' h' => Z.eqb l l' && Z.eqb h h'
  | KAlign e m, KAlign e' m' => expr_eqb e e' && Z.eqb m m'
  | KRange e l h, KRange e' l' h' => expr_eqb e e' && Z.eqb l l' && Z.eqb h h'
  | KWr a n, KWr a' n' => saddr_eqb a a' && Z.eqb n n'
  | KDisj a n b m, KDisj a' n' b' m' => saddr_eqb a a' && Z.eqb n n' && saddr_eqb b b' && Z.eqb m m'
  | _, _ => false
  end%bool.

Lemma kentry_eqb_eq : forall K K', kentry_eqb K K' = true -> K = K'.
Proof.
  intros K K' H; destruct K, K'; cbn [kentry_eqb] in H; try discriminate;
    repeat (apply andb_prop in H as [H ?]);
    repeat match goal with
      | G : saddr_eqb _ _ = true |- _ => apply saddr_eqb_eq in G
      | G : expr_eqb _ _ = true |- _ => apply expr_eqb_eq in G
      | G : Z.eqb _ _ = true |- _ => apply Z.eqb_eq in G
      | G : Nat.eqb _ _ = true |- _ => apply Nat.eqb_eq in G
      end; subst; try reflexivity;
    repeat match goal with x : saddr |- _ => destruct x end; cbn [a_base a_off] in *; subst; reflexivity.
Qed.

(* [comment removed for export] *)
Definition kn_incl (kn1 kn2 : list kentry) : bool :=
  forallb (fun K => existsb (kentry_eqb K) kn2) kn1.

Lemma know_ok_incl : forall segs E M kn1 kn2,
  kn_incl kn1 kn2 = true -> know_ok segs E M kn2 -> know_ok segs E M kn1.
Proof.
  intros segs E M kn1 kn2 Hi HK. unfold know_ok in *. apply Forall_forall. intros K HinK.
  pose proof (proj1 (forallb_forall _ _) Hi K HinK) as HE. apply existsb_exists in HE as (K' & Hin' & Heq).
  apply kentry_eqb_eq in Heq. subst K'. exact (proj1 (Forall_forall _ _) HK K Hin').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section KreadBytes.
  Variable segs : list Segment.

  Fixpoint kread_bytes (kn : list kentry) (b : expr) (k : Z) (n : nat) : option (list Z) :=
    match n with
    | O => Some []
    | S n' => match kread segs kn b k 1, kread_bytes kn b (k + 1) n' with
              | Some (ELit z), Some r => Some (z :: r)
              | _, _ => None
              end
    end.

  Lemma zbv8_of_64 : forall z, Z_to_bv 8 (bv_unsigned (Z_to_bv 64 z)) = Z_to_bv 8 z.
  Proof.
    intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
    change (bv_modulus 64) with (2 ^ 64)%Z. change (bv_modulus 8) with (2 ^ 8)%Z.
    rewrite <- (Z.mod_mod_divide z (2 ^ 64) (2 ^ 8)) by (exists (2 ^ 56)%Z; reflexivity). reflexivity.
  Qed.

  Lemma rdn_of_kread_bytes : forall E M kn b n k zs,
    know_ok segs E M kn -> kread_bytes kn b k n = Some zs ->
    flat E (SA b k) (Z.of_nat n) ->
    rdn segs M (adenot E (SA b k)) n = Some (map (fun z => Z_to_bv 8 z) zs).
  Proof.
    intros E M kn b n. induction n as [|n IH]; intros k zs HK Hkb Hfl.
    - cbn in Hkb. injection Hkb as <-. reflexivity.
    - cbn [kread_bytes] in Hkb.
      destruct (kread segs kn b k 1) as [[z| | | | | | |]|] eqn:K1; try discriminate.
      destruct (kread_bytes kn b (k + 1) n) as [r|] eqn:KR; try discriminate. injection Hkb as <-.
      (first [ pose proof (Hfl) as dR_1; dand4 dR_1 as F1 F2 F3 F4 | pose proof Hfl as (F1 & F2 & F3 & F4) ]). unfold estart in F1, F2, F4. cbn [a_base a_off] in F1, F2, F4.
      pose proof (kread_rdn segs E M kn b k 1 (ELit z) HK K1 ltac:(lia) ltac:(lia)
                    ltac:(unfold flat, estart; cbn [a_base a_off]; lia)) as R1.
      cbn [rdn] in R1 |- *.
      destruct (match M (adenot E (SA b k)) with Some b0 => Some b0 | None => seg_rom segs (adenot E (SA b k)) end) as [b0|];
        [|discriminate].
      injection R1 as E0.
      destruct n as [|n'].
      { cbn in KR. injection KR as <-. cbn [rdn map]. f_equal. f_equal. rewrite E0. cbn [edenot]. apply zbv8_of_64. }
      specialize (IH (k + 1)%Z r HK KR ltac:(unfold flat, estart; cbn [a_base a_off]; lia)).
      replace (adenot E (SA b (k + 1))) with (adenot E (SA b k) + 1)%bv in IH.
      2:{ unfold adenot, v_addi. cbn [a_base a_off]. apply bv_eq.
          rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_unsigned 1) with 1%Z.
          rewrite <- Zplus_mod_idemp_l. f_equal. lia. }
      rewrite IH. cbn [map]. f_equal. f_equal. rewrite E0. cbn [edenot]. apply zbv8_of_64.
  Qed.
End KreadBytes.
