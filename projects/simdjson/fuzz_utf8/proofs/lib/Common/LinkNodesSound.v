(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import SymStepR AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.simdjson.fuzz_utf8.lib.Common Require Import AsanNodesAux. From OSSVerify.Proofs.simdjson.fuzz_utf8.lib Require Import ExecNodes ExecNodesSound LinkNodes.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import LNK.
Open Scope Z_scope.

Module LNKS.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
  Context {fx : FPState}.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.

  (* [comment removed for export] *)
  Lemma low_part_eq : forall (vx vne : word) (j : Z), 1 <= j <= 63 ->
    bv_unsigned vx - bv_unsigned vx mod 2 ^ j = bv_unsigned vne ->
    bv_unsigned (alu64 ALU_SUB vx vne) = bv_unsigned vx mod 2 ^ j.
  Proof.
    intros vx vne j Hj Hhi. rewrite u_sub64.
    pose proof (u64_range vx) as Hx. pose proof (Z.mod_pos_bound (bv_unsigned vx) (2 ^ j) ltac:(apply Z.pow_pos_nonneg; lia)) as Hm.
    assert (Hp : 2 ^ j < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
    replace (bv_unsigned vx - bv_unsigned vne) with (bv_unsigned vx mod 2 ^ j) by lia.
    apply Z.mod_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_and_high : forall E x j m, 1 <= j <= 63 -> (m = mhi_pos j \/ m = mhi_neg j) ->
    bv_unsigned (edenot E (EAlu ALU_AND x (ELit m))) = bv_unsigned (edenot E x) - bv_unsigned (edenot E x) mod 2 ^ j.
  Proof.
    intros E x j m Hj Hm. cbn [edenot].
    assert (EQ : (Z_to_bv 64 m : word) = Z_to_bv 64 (- 2 ^ j)).
    { apply bv_eq. rewrite !u_lit64a. destruct Hm as [-> | ->]; unfold mhi_pos, mhi_neg, two64; [|reflexivity].
      assert (Hp : 0 < 2 ^ j < 2 ^ 64) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
      rewrite (Z.mod_small (2 ^ 64 - 2 ^ j)) by lia.
      replace (- 2 ^ j) with ((2 ^ 64 - 2 ^ j) + (-1) * 2 ^ 64) by lia. rewrite Z_mod_plus_full. symmetry. apply Z.mod_small. lia. }
    rewrite EQ, and_highmask_val by lia.
    pose proof (u64_range (edenot E x)) as Hx.
    pose proof (Z.mod_pos_bound (bv_unsigned (edenot E x)) (2 ^ j) ltac:(apply Z.pow_pos_nonneg; lia)) as Hmod.
    pose proof (Z.mod_le (bv_unsigned (edenot E x)) (2 ^ j) ltac:(lia) ltac:(lia)) as Hle.
    apply u_small. lia.
  Qed.

  Lemma u_and_low : forall E x j, 1 <= j <= 63 ->
    bv_unsigned (edenot E (EAlu ALU_AND x (ELit (2 ^ j - 1)))) = bv_unsigned (edenot E x) mod 2 ^ j.
  Proof.
    intros E x j Hj. cbn [edenot]. rewrite and_lowmask_val by lia.
    pose proof (Z.mod_pos_bound (bv_unsigned (edenot E x)) (2 ^ j) ltac:(apply Z.pow_pos_nonneg; lia)) as Hmod.
    assert (Hp : 2 ^ j < 2 ^ 64) by (apply Z.pow_lt_mono_r; lia).
    apply u_small. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma u_srl_form : forall E x j, 1 <= j <= 63 ->
    bv_unsigned (edenot E (srl_form x j)) = bv_unsigned (edenot E x) - bv_unsigned (edenot E x) mod 2 ^ j.
  Proof.
    intros E x j Hj. unfold srl_form. cbn [edenot]. rewrite u_mul64, u_srl64, !u_lit64.
    pose proof (u64_range (edenot E x)) as Hx. set (ux := bv_unsigned (edenot E x)) in *.
    assert (Hp : 0 < 2 ^ j < 2 ^ 64) by (split; [apply Z.pow_pos_nonneg; lia | apply Z.pow_lt_mono_r; lia]).
    unfold two64. rewrite (Z.mod_small (2 ^ j)) by lia. rewrite (Z.mod_small j) by lia. rewrite (Z.mod_small j) by lia.
    pose proof (Z.div_mod ux (2 ^ j) ltac:(lia)) as Hdm.
    pose proof (Z.mod_pos_bound ux (2 ^ j) ltac:(lia)) as Hm.
    replace (2 ^ j * (ux / 2 ^ j)) with (ux - ux mod 2 ^ j) by lia.
    apply Z.mod_small. lia.
  Qed.

  Lemma lin_eq0_sound : forall E M k a b, know_ok SEGS E M k -> lin_eq0 k a b = true ->
    bv_unsigned (edenot E a) = bv_unsigned (edenot E b).
  Proof.
    intros E M k a b HK H. unfold lin_eq0 in H. apply andb_prop in H as [H1 H2].
    pose proof (lin_ge0_sound SEGS E M k _ _ HK H1) as G1. pose proof (lin_ge0_sound SEGS E M k _ _ HK H2) as G2.
    cbn [xt_den] in G1, G2. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma link_fact_ok : forall E M k x j ne lo hi, know_ok SEGS E M k -> 1 <= j <= 63 ->
    high_linked k x j ne = true -> erange k (EAlu ALU_AND x (ELit (2 ^ j - 1))) = Some (lo, hi) ->
    kentry_ok SEGS E M (KRange (esub x ne) lo hi).
  Proof.
    intros E M k x j ne lo hi HK Hj Hl Hr.
    pose proof (erange_sound SEGS E M k _ lo hi HK Hr) as Hb. rewrite (u_and_low E x j Hj) in Hb.
    assert (Hhi : bv_unsigned (edenot E x) - bv_unsigned (edenot E x) mod 2 ^ j = bv_unsigned (edenot E ne)).
    { unfold high_linked in Hl. apply orb_prop in Hl as [Hl|HS].
      2:{ (* [comment removed for export] *) rewrite <- (lin_eq0_sound E M k _ _ HK HS). symmetry. apply u_srl_form. lia. }
      apply orb_prop in Hl as [Hl|HB].
      - apply orb_prop in Hl as [Hl|Hl];
          rewrite <- (lin_eq0_sound E M k _ _ HK Hl); symmetry; apply u_and_high; [lia| |lia|]; [left|right]; reflexivity.
      - (* [comment removed for export] *)
        unfold block_linked in HB.
        destruct (xlo k x) as [l|] eqn:Hxl; [|discriminate]. destruct (xhi k x) as [h|] eqn:Hxh; [|discriminate].
        destruct (erange k ne) as [[nl nh]|] eqn:Hne; [|discriminate].
        apply andb_prop in HB as [HB Hc2]. apply andb_prop in HB as [HB Hc1]. apply andb_prop in HB as [Hl0 Hq].
        apply Z.leb_le in Hl0. apply Z.eqb_eq in Hq. apply Z.eqb_eq in Hc1. apply Z.eqb_eq in Hc2.
        pose proof (xlo_sound SEGS E M k x l HK Hxl) as Hl'. pose proof (xhi_sound SEGS E M k x h HK Hxh) as Hh'.
        pose proof (erange_sound SEGS E M k ne nl nh HK Hne) as Hn'.
        set (ux := bv_unsigned (edenot E x)) in *.
        assert (Hp : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
        assert (Hq' : ux / 2 ^ j = l / 2 ^ j).
        { pose proof (Z.div_le_mono l ux (2 ^ j) Hp Hl'). pose proof (Z.div_le_mono ux h (2 ^ j) Hp Hh'). lia. }
        pose proof (Z.div_mod ux (2 ^ j) ltac:(lia)) as Hdm. rewrite Hq' in Hdm. lia. }
    cbn [kentry_ok]. unfold esub. rewrite mkAlu_denot. rewrite (low_part_eq _ _ j Hj Hhi). exact Hb.
  Qed.

  (* [comment removed for export] *)
  Theorem xn_soundF : forall args, node1_stmtF SEGS A nx0 LIMIT SINV argH FS0 always (LNK.xn args).
  Proof.
    intros args cs cs' E R FULL model T HC _ Hn Hk. unfold xn in Hn.
    destruct args as [|x [|jl [|ne rest]]]; try discriminate;
      destruct jl as [j|v|o a b|o a b|o a b|o a b|sx lo0 n0 e0|sx kb ib nb]; try discriminate;
      destruct rest as [|e4 rest']; try discriminate.
    destruct (Z.leb 1 j && Z.leb j 63 && high_linked (kn cs) x j ne)%bool eqn:Hg; [|discriminate].
    apply andb_prop in Hg as [Hg Hl]. apply andb_prop in Hg as [Hj1 Hj2]. apply Z.leb_le in Hj1. apply Z.leb_le in Hj2.
    destruct (erange (kn cs) (EAlu ALU_AND x (ELit (2 ^ j - 1)))) as [[lo hi]|] eqn:Hr; [|discriminate].
    injection Hn as <-.
    eapply EXNS.set_kn_sound; [exact HC | | exact Hk].
    constructor; [| exact (co_know _ _ _ _ _ _ _ _ _ _ _ HC)].
    exact (link_fact_ok E _ (kn cs) x j ne lo hi (co_know _ _ _ _ _ _ _ _ _ _ _ HC) ltac:(lia) Hl Hr).
  Qed.

  Theorem xn_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (LNK.xn args).
  Proof. intros args. apply node1_stmtF_stmt. apply xn_soundF. Qed.
End Sound.

End LNKS.
