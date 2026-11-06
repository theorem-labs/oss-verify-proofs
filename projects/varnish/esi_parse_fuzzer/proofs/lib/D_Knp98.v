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
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require SymRun SymDrive SymDe08 LibK2dm D_Kn21w.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.CatExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.WallSim.SeqExec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StepTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.StoreOk OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.MemSplit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymExec2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun.SymEo0r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymRun OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDrive OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.SymDe08 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.LibK2dm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.D_Kn21w.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations. Import SX2. Import SX2S.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition kimg_within (kn : list kentry) (ilo ihi : Z) : bool :=
  forallb (fun K => match K with KImg lo hi => ((ilo <=? lo) && (hi <=? ihi))%Z%bool | _ => true end) kn.

(* [comment removed for export] *)
Definition kimg_cov (kn : list kentry) (x : Z) : Prop :=
  exists lo hi, In (KImg lo hi) kn /\ (lo <= x < hi)%Z.

Lemma kimg_within_cov : forall kn ilo ihi x,
  kimg_within kn ilo ihi = true -> kimg_cov kn x -> (ilo <= x < ihi)%Z.
Proof.
  (intros kn ilo ihi x H; (first [ intro dR_9; dex2 dR_9 as lo hi; destruct dR_9 as [Hin Hx] | intro dR_9; dand4 dR_9 as lo hi Hin Hx | intros (lo & hi & Hin & Hx) ])). unfold kimg_within in H.
  pose proof (proj1 (forallb_forall _ _) H (KImg lo hi) Hin) as Hb. cbn beta iota in Hb.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
Qed.

Section Vis.
  Variable segs : list Segment.

  Definition in_seg (x : word) : Prop := exists sg, find_segment segs (bv_unsigned x) 1 = Some sg.

  (* [comment removed for export] *)
  Lemma rdn_some_vis : forall M n (a : word) bs,
    rdn segs M a n = Some bs ->
    forall j, (j < n)%nat ->
      M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None \/ in_seg (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)).
  Proof.
    intros M n. induction n as [|n IH]; intros a bs Hr j Hj; [lia|].
    cbn [rdn] in Hr.
    destruct j as [|j].
    - rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned.
      destruct (M a) as [b|] eqn:Hm; [left; congruence|].
      destruct (seg_rom segs a) as [b|] eqn:Hs; [| discriminate]. right.
      unfold seg_rom, memory_read in Hs. change (Z.of_N 1) with 1%Z in Hs.
      destruct (find_segment segs (bv_unsigned a) 1) as [sg|] eqn:Hf; [exists sg; exact Hf| discriminate].
    - assert (Hr' : exists rest, rdn segs M (a + 1) n = Some rest).
      { destruct (match M a with Some b => Some b | None => seg_rom segs a end); [|discriminate].
        destruct (rdn segs M (a + 1) n) as [rest|]; [exists rest; reflexivity| discriminate]. }
      destruct Hr' as [rest Hrest].
      replace (Z_to_bv 64 (bv_unsigned a + Z.of_nat (S j))) with (Z_to_bv 64 (bv_unsigned (a + 1) + Z.of_nat j)).
      + apply (IH (a + 1) rest Hrest). lia.
      + rewrite <- !word_add_nat. rewrite word1_nat, nat_to_word_add_merge. reflexivity.
  Qed.

  Lemma store_ok_some_vis : forall M n (a : word),
    RiscvSemantics.store_ok segs M a n = true ->
    forall j, (j < n)%nat ->
      M (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)) <> None \/ in_seg (Z_to_bv 64 (bv_unsigned a + Z.of_nat j)).
  Proof.
    intros M n. induction n as [|n IH]; intros a Hs j Hj; [lia|].
    cbn [RiscvSemantics.store_ok] in Hs.
    destruct (wview segs M a) as [b|] eqn:Hv; [|discriminate].
    destruct j as [|j].
    - rewrite Nat2Z.inj_0, Z.add_0_r, Z_to_bv_bv_unsigned.
      unfold wview in Hv. destruct (M a) as [b'|] eqn:Hm; [left; congruence|].
      right. destruct (find_segment segs (bv_unsigned a) 1) as [sg|] eqn:Hf; [exists sg; exact Hf| discriminate].
    - replace (Z_to_bv 64 (bv_unsigned a + Z.of_nat (S j))) with (Z_to_bv 64 (bv_unsigned (a + 1) + Z.of_nat j)).
      + apply (IH (a + 1) Hs). lia.
      + rewrite <- !word_add_nat. rewrite word1_nat, nat_to_word_add_merge. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition vis (M : word -> option byte) (kept : list kentry) (x : word) : Prop :=
    M x <> None \/ in_seg x \/ kimg_cov kept (bv_unsigned x).

  Lemma know_ok_keep_vis : forall E M M' kn rs,
    know_ok segs E M kn ->
    Forall (fun r : frange => match r with (ub, uk, un) => flat E (SA ub uk) un end) rs ->
    (forall x : word, outside_all E rs x -> vis M (kn_keep kn rs) x -> M' x = M x) ->
    know_ok segs E M' (kn_keep kn rs).
  Proof.
    intros E M M' kn rs HK Hfl OUT.
    unfold know_ok. apply Forall_forall. intros K HinF.
    pose proof HinF as HinK. unfold kn_keep in HinF.
    apply filter_In in HinF as [Hin Hb].
    pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
    assert (OUTF : forall b k n (x : word), apart_all kn rs b k n = true ->
              (estart E (SA b k) <= bv_unsigned x < estart E (SA b k) + n)%Z -> vis M (kn_keep kn rs) x -> M' x = M x).
    { intros b k n x H Hx Hv. apply OUT; [|exact Hv]. eapply footprint_outside; eassumption. }
    destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2];
      cbn [kn_keep1] in Hb.
    - (* [comment removed for export] *)
      cbn [kentry_ok] in HKK |- *.
      (first [ dand3 HKK as Hw Hf Hr | destruct HKK as (Hw & Hf & Hr) ]). split; [exact Hw|]. split; [exact Hf|].
      rewrite <- Hr. symmetry. apply rdn_agree. intros j Hj. symmetry.
      pose proof (flat_u E _ _ Hf) as Hub. (first [ dand4 Hf as G1 G2 G3 G4 | destruct Hf as (G1 & G2 & G3 & G4) ]).
      apply (OUTF b k (Z.of_nat w)); [exact Hb| |].
      + rewrite u_small by lia. unfold estart in *. cbn [a_base a_off] in *. lia.
      + destruct (rdn_some_vis M w (adenot E (SA b k)) _ Hr j Hj) as [X|X]; [left; exact X| right; left; exact X].
    - (* [comment removed for export] *)
      destruct len as [l| | | | | | |]; try discriminate Hb.
      apply andb_prop in Hb as [Hl Hap]. apply andb_prop in Hl as [Hl0 Hl1].
      apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
      cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hz).
      assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
      rewrite El in *. split; [exact Hf|].
      pose proof (flat_u E _ _ Hf) as Hub. (first [ dand4 Hf as G1 G2 G3 G4 | destruct Hf as (G1 & G2 & G3 & G4) ]).
      intros i Hi. rewrite (OUTF b k l); [apply Hz; exact Hi | exact Hap | |].
      + rewrite u_small by lia. lia.
      + left. rewrite (Hz i Hi). discriminate.
    - (* [comment removed for export] *)
      destruct len as [l| | | | | | |]; try discriminate Hb.
      apply andb_prop in Hb as [Hl Hap]. apply andb_prop in Hl as [Hl0 Hl1].
      apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
      cbn [kentry_ok] in HKK |- *. (first [ dand3 HKK as Hf Hlen Hz | destruct HKK as (Hf & Hlen & Hz) ]).
      assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia).
      rewrite El in *. split; [exact Hf|]. split; [exact Hlen|].
      pose proof (flat_u E _ _ Hf) as Hub. (first [ dand4 Hf as G1 G2 G3 G4 | destruct Hf as (G1 & G2 & G3 & G4) ]).
      intros i Hi. rewrite (OUTF b k l); [apply Hz; exact Hi | exact Hap | |].
      + rewrite u_small by lia. lia.
      + left. rewrite (Hz i Hi). discriminate.
    - (* [comment removed for export] *)
      apply andb_prop in Hb as [Hl Hap]. apply andb_prop in Hl as [Hl Hhi]. apply andb_prop in Hl as [Hlo Hlh].
      apply Z.leb_le in Hlo. apply Z.ltb_lt in Hlh. apply Z.leb_le in Hhi.
      cbn [kentry_ok] in HKK |- *. (first [ dand3 HKK as H0 H1 Hnone | destruct HKK as (H0 & H1 & Hnone) ]). split; [exact H0|]. split; [exact H1|].
      intros i Hi. rewrite (OUTF (ELit 0) lo (hi - lo)%Z); [apply Hnone; exact Hi | exact Hap | |].
      + unfold estart. cbn [a_base a_off]. rewrite edenot_lit0. rewrite u_small by lia. lia.
      + right; right. exists lo, hi. split; [exact HinK|]. rewrite u_small by lia. exact Hi.
    - (* [comment removed for export] *) exact HKK.
    - (* [comment removed for export] *) exact HKK.
    - (* [comment removed for export] *)
      apply andb_prop in Hb as [Hn Hap]. apply Z.leb_le in Hn.
      cbn [kentry_ok] in HKK |- *.
      destruct HKK as (Hf & Hst). split; [exact Hf|].
      pose proof (flat_u E _ _ Hf) as Hub. (first [ dand4 Hf as G1 G2 G3 G4 | destruct Hf as (G1 & G2 & G3 & G4) ]).
      intros d m Hd Hm. rewrite (store_ok_agree segs m M M'); [apply Hst; assumption|].
      intros j Hj. rewrite word_add_nat. apply (OUTF b k n); [exact Hap| |].
      + rewrite (u_small (estart E (SA b k) + d)) by lia. rewrite u_small by lia. lia.
      + destruct (store_ok_some_vis M m (Z_to_bv 64 (estart E (SA b k) + d)) (Hst d m Hd Hm) j Hj) as [X|X];
          [left; exact X| right; left; exact X].
    - (* [comment removed for export] *) exact HKK.
  Qed.

  (* [comment removed for export] *)
  Lemma know_ok_keep2_vis : forall E M M' kn rs vict,
    know_ok segs E M kn ->
    Forall (fun r : frange => match r with (ub, uk, un) => flat E (SA ub uk) un end) rs ->
    (forall x : word, outside_all E rs x -> vis M (kn_keep kn rs) x -> M' x = M x) ->
    (forall x : word, outside_all E vict x -> M x <> None -> M' x <> None) ->
    know_ok segs E M' (kn_keep2 kn rs vict).
  Proof.
    intros E M M' kn rs vict HK Hfl OUT DOM. unfold kn_keep2. apply know_ok_app.
    - eapply know_ok_keep_vis; eassumption.
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
End Vis.
