(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec Image.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface Lept_kit Lept_iface.
Import ListNotations.
Open Scope Z_scope.

Lemma image_bytes_length : forall n A bs, image_bytes asegs A n = Some bs -> length bs = n.
Proof.
  induction n as [|n IH]; intros A bs H; cbn in H; [injection H as <-; reflexivity|].
  destruct (seg_rom asegs (wa A)); [|discriminate]. destruct (image_bytes asegs (A + 1) n) eqn:E; [|discriminate].
  injection H as <-. cbn. f_equal. exact (IH _ _ E).
Qed.

Lemma lit_facts : forall S l (m : mem), In (S, l) LEPT_LITS -> mem_inv asegs m ->
  exists str slack : list byte, bytes_at asegs m S (str ++ Z_to_bv 8 0 :: slack) /\ ~ In (Z_to_bv 8 0) str
    /\ Z.of_nat (length str) + 1 = l /\ Z.of_nat (length slack) = (- (S + l)) mod 8
    /\ 0x10000 <= S /\ S + l + Z.of_nat (length slack) <= 0x6dda4 /\ l < 97.
Proof.
  intros S l m Hin MI. pose proof lept_lits_ok as OK. rewrite forallb_forall in OK. specialize (OK _ Hin).
  unfold lit_ok, lit_pad in OK. cbn [fst snd] in OK.
  set (pad := (- (S + l)) mod 8) in *. assert (PD : 0 <= pad < 8) by (unfold pad; apply Z.mod_pos_bound; lia).
  destruct (image_bytes asegs S (Z.to_nat (l + pad))) as [bs|] eqn:IB; [|discriminate].
  repeat (apply andb_prop in OK; destruct OK as [OK ?]).
  apply Z.leb_le in H2. apply Z.leb_le in H1. apply Z.ltb_lt in H0. apply Z.ltb_lt in H.
  pose proof (image_bytes_length _ _ _ IB) as LB.
  destruct (rev (firstn (Z.to_nat l) bs)) as [|z rstr] eqn:RV; [discriminate|].
  apply andb_prop in H3. destruct H3 as [Z0 NZ]. apply Z.eqb_eq in Z0.
  assert (EZ : z = Z_to_bv 8 0) by (apply bv_eq; rewrite Z0; reflexivity).
  assert (EF : firstn (Z.to_nat l) bs = rev rstr ++ [z]) by (rewrite <- (rev_involutive (firstn _ bs)), RV; reflexivity).
  assert (EB : bs = (rev rstr ++ [z]) ++ skipn (Z.to_nat l) bs) by (rewrite <- EF; symmetry; apply firstn_skipn).
  assert (LF : length (firstn (Z.to_nat l) bs) = Z.to_nat l) by (apply firstn_length_le; lia).
  exists (rev rstr), (skipn (Z.to_nat l) bs).
  assert (LS : length (skipn (Z.to_nat l) bs) = Z.to_nat pad) by (rewrite length_skipn; lia).
  assert (LR : Z.of_nat (length (rev rstr)) + 1 = l) by (rewrite EF, length_app in LF; cbn [length] in LF; lia).
  split.
  - rewrite <- EZ. replace (rev rstr ++ z :: skipn (Z.to_nat l) bs) with bs by (rewrite EB at 1; rewrite <- app_assoc; reflexivity).
    apply ro_bytes_at; [exact MI| lia| rewrite LB; lia| apply ro_bytes_b_sound; exact OK].
  - split.
    + intros Hc. apply in_rev in Hc. rewrite forallb_forall in NZ. specialize (NZ _ Hc). vm_compute in NZ. discriminate NZ.
    + rewrite LS. repeat split; lia.
Qed.

Section Lits.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.

Lemma lept_args_of_lit : forall Σ (m : mem) (sp : word) lo D kinds ws, ART RT Σ m -> mem_inv asegs m ->
  rt_sp0 RT Σ - STACK_WIN <= lo -> SEGTOP_A <= D ->
  lept_args_lit kinds ws -> lept_args RT Σ m sp lo D kinds ws.
Proof using AF GP.
  intros Σ m sp lo D kinds. induction kinds as [|k ks IH]; intros ws HA MI LO HD H; [exact I|].
  destruct ws as [|w ws]; [destruct k; exact H|]. destruct k; cbn in *; [| exact (IH _ HA MI LO HD H)].
  destruct H as [(l & Hin) H]. split; [| exact (IH _ HA MI LO HD H)].
  destruct (lit_facts _ _ m Hin MI) as (str & slack & B & NZ & L & LS & R1 & R2 & R3). exists str.
  pose proof (gp_acc_lits RT GP Σ m HA) as AL. rewrite Forall_forall in AL. specialize (AL _ Hin). cbn [fst snd] in AL.
  pose proof (af_sp0_range RT AF Σ m HA) as SP0R. unfold SEGTOP_A, STACK_WIN in *.
  split; [| lia]. exists slack. rewrite L.
  split; [exact B|]. split; [exact NZ|]. split; [rewrite LS; lia|]. split; [lia|]. split; [lia|].
  split; [| right; lia].
  split; [intros _; split; [exact AL| right; right; right; unfold SEGTOP_A; lia]| left; lia].
Qed.
End Lits.
