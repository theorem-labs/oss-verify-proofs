(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec StoreOk ShapeAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxPlanSound2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Fixpoint bytes_readable (segs : list Segment) (k : list kentry) (b : expr) (off : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => (kn_readable segs k k b off 1 && bytes_readable segs k b (off + 1) n')%bool
  end.

Definition node_joinx_m (segs : list Segment) (nx0 : nat) (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off; ELit nz] =>
      let n := Z.to_nat nz in
      if (Nat.leb 1 n && Nat.leb n 8 && fresh_ok nx0 cs && expr_vars_lt (nxt cs) b && bytes_readable segs (kn cs) b off n)%bool then
        let v := nxt cs in Some (bump (add_kn cs [KWord (SA b off) n (EVar v)]) 1)
      else None
  | _ => None
  end.

Lemma bytes_readable_sound : forall segs E M k b n off,
  know_ok segs E M k -> (1 <= n)%nat -> bytes_readable segs k b off n = true ->
  flat E (SA b off) (Z.of_nat n)
  /\ forall j, (j < n)%nat -> rd1 segs M (Z_to_bv 64 (estart E (SA b off) + Z.of_nat j)) <> None.
Proof.
  intros segs E M k b n. induction n as [|n IH]; intros off HK Hn H; [lia|].
  cbn [bytes_readable] in H. apply andb_prop in H as [H1 H2].
  destruct (kn_readable_sound segs E M k M k b off 1 HK HK ltac:(lia) ltac:(lia) H1) as [F1 [bs [R1 L1]]].
  assert (B1 : rd1 segs M (Z_to_bv 64 (estart E (SA b off))) <> None).
  { pose proof (rdn_rd1 segs M 1 (adenot E (SA b off)) bs 0 R1 ltac:(lia)) as X.
    rewrite w_add_nat, (flat_u E _ _ F1) in X. cbn [Z.of_nat] in X. rewrite Z.add_0_r in X. exact X. }
  destruct n as [|n'].
  - split; [exact F1|]. intros j Hj. replace j with 0%nat by lia. cbn [Z.of_nat]. rewrite Z.add_0_r. exact B1.
  - destruct (IH (off + 1) HK ltac:(lia) H2) as [F2 B2].
    split; [unfold flat, estart in *; cbn [a_base a_off] in *; lia|].
    intros j Hj. destruct j as [|j'].
    + cbn [Z.of_nat]. rewrite Z.add_0_r. exact B1.
    + specialize (B2 j' ltac:(lia)). unfold estart in *; cbn [a_base a_off] in *.
      replace (bv_unsigned (edenot E b) + off + Z.of_nat (S j')) with (bv_unsigned (edenot E b) + (off + 1) + Z.of_nat j') by lia.
      exact B2.
Qed.

(* [comment removed for export] *)
Definition node_join_alt (segs : list Segment) (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off; ELit nz; b'; ELit off'] =>
      let n := Z.to_nat nz in let k := kn cs in
      if (Nat.leb 1 n && Nat.leb n 8 && flat_x k b off (ELit (Z.of_nat n)) && flat_x k b' off' (ELit (Z.of_nat n))
          && respell_ok k (mkAluK k ALU_ADD b (ELit off)) (mkAluK k ALU_ADD b' (ELit off')))%bool then
        match kread_bytes segs n k b' off' with
        | Some bs => Some (add_kn cs [KWord (SA b off) n (ELit (zbytes_le_to_Z bs))])
        | None => None
        end
      else None
  | _ => None
  end.

Lemma sum_adenot : forall segs E M k b off, know_ok segs E M k -> edenot E (mkAluK k ALU_ADD b (ELit off)) = adenot E (SA b off).
Proof.
  intros segs E M k b off HK. rewrite (mkAluK_denot segs E M k _ _ _ HK). cbn [edenot]. apply bv_eq.
  rewrite u_add64, u_lit64. unfold adenot, v_addi. cbn [a_base a_off]. rewrite Z_to_bv_unsigned, bv_wrap64_mod. unfold two64.
  rewrite Z.add_mod_idemp_r by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition node_join_zero (args : list expr) (cs : acs) : option acs :=
  match args with
  | [b; ELit off; ELit nz] =>
      let n := Z.to_nat nz in
      if (Nat.leb 1 n && Nat.leb n 8 && Z.eqb nz (Z.of_nat n) && kzero_x (kn cs) (kn cs) b off (ELit nz))%bool then
        Some (add_kn cs [KWord (SA b off) n (ELit (zbytes_le_to_Z (repeat 0%Z n)))])
      else None
  | _ => None
  end.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis NX0_spw : CAP.expr_vars_lt nx0 e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

Theorem node_joinx_m_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_joinx_m SEGS nx0 args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_joinx_m in Hn.
  destruct args as [|b [|[off| | | | | | |] [|[nz| | | | | | |] [|]]]]; try discriminate Hn.
  set (n := Z.to_nat nz) in *.
  destruct (Nat.leb 1 n && Nat.leb n 8 && fresh_ok nx0 cs && CAP.expr_vars_lt (nxt cs) b
            && bytes_readable SEGS (kn cs) b off n)%bool eqn:Ht; [|discriminate].
  apply andb_prop in Ht as [Ht Hrd]. apply andb_prop in Ht as [Ht Hvb]. apply andb_prop in Ht as [Ht Hfresh].
  apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  injection Hn as <-.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (bytes_readable_sound SEGS E _ (kn cs) b n off HK H1 Hrd) as [Hfl Hpt].
  destruct (rdn_defined SEGS (CXS.Mr A argH E cs model FULL) n (adenot E (SA b off))) as [bs [Hrdn Hlen]];
    [rewrite (flat_u E _ _ Hfl); destruct Hfl as (?&?&?&?); lia | rewrite (flat_u E _ _ Hfl); exact Hpt |].
  destruct (CXS.fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs) in *.
  set (a := Z_to_bv 64 (bytes_le_to_Z bs)). set (E' := CXS.ext1 E v a).
  assert (Hag : env_agree v E E') by apply CXS.ext1_agree.
  pose proof (CXS.cs_ok_agree SEGS A nx0 LIMIT NX0_spw SINV argH ISP argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
  assert (Hbv : edenot E' b = edenot E b) by (symmetry; eapply (CXS.edenot_agree' v); [exact Hag | exact Hvb]).
  assert (HMr : CXS.Mr A argH E' cs model FULL = CXS.Mr A argH E cs model FULL).
  { unfold CXS.Mr. rewrite (CXS.hid_agree A nx0 argH argH_agree v E E' cs model Hag Fle Fallow). reflexivity. }
  apply (Hk E' R FULL model); [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag] | | reflexivity].
  assert (HKf : know_ok SEGS E' (CXS.Mr A argH E' cs model FULL) (KWord (SA b off) n (EVar v) :: kn cs)).
  { constructor; [|exact (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC')].
    cbn [kentry_ok]. split; [exact H8|].
    assert (Had : adenot E' (SA b off) = adenot E (SA b off)) by (unfold adenot; cbn [a_base a_off]; rewrite Hbv; reflexivity).
    split; [unfold flat, estart in *; cbn [a_base a_off] in *; rewrite Hbv; exact Hfl|].
    rewrite HMr, Had, Hrdn. f_equal. cbn [edenot]. unfold E'. rewrite CXS.ext1_at. unfold a.
    unfold word_to_le_bytes. pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Hlen in Bb. pose proof (bytes_le_to_Z_nonneg bs) as Bn.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Hlen. symmetry. apply Z_to_le_bytes_to_Z. }
  destruct HC'; constructor; cbn [bump add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know s_pc s_next kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset]; try assumption; try reflexivity.
Qed.

Theorem node_join_alt_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_join_alt SEGS args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_join_alt in Hn.
  destruct args as [|b [|[off| | | | | | |] [|[nz| | | | | | |] [|b' [|[off'| | | | | | |] [|]]]]]]; try discriminate Hn.
  set (n := Z.to_nat nz) in *.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Ht; [|discriminate] end.
  apply andb_prop in Ht as [Ht Heqb]. apply andb_prop in Ht as [Ht Hfx']. apply andb_prop in Ht as [Ht Hfx].
  apply andb_prop in Ht as [H1 H8]. apply Nat.leb_le in H1. apply Nat.leb_le in H8.
  destruct (kread_bytes SEGS n (kn cs) b' off') as [zs|] eqn:Hr; [|discriminate].
  injection Hn as <-.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (flat_x_sound SEGS E _ (kn cs) b off (ELit (Z.of_nat n)) HK Hfx) as (F1 & F2 & F3).
  pose proof (flat_x_sound SEGS E _ (kn cs) b' off' (ELit (Z.of_nat n)) HK Hfx') as (G1 & G2 & G3).
  rewrite edenot_lit, u64_lit in F2, F3, G2, G3 by lia.
  pose proof (respell_ok_sound SEGS E _ (kn cs) _ _ HK Heqb) as Heq.
  rewrite (sum_adenot SEGS E _ (kn cs) b off HK), (sum_adenot SEGS E _ (kn cs) b' off' HK) in Heq.
  assert (Hfl : flat E (SA b off) (Z.of_nat n)) by (unfold flat; lia).
  assert (Hfl' : flat E (SA b' off') (Z.of_nat n)) by (unfold flat; lia).
  assert (Hst : estart E (SA b off) = estart E (SA b' off')) by (rewrite <- (flat_u E _ _ Hfl), <- (flat_u E _ _ Hfl'), Heq; reflexivity).
  destruct (kread_bytes_sound SEGS E _ (kn cs) n b' off' zs HK Hr G1 G2) as [bs (Lb & Mb & Rb)].
  assert (Hrefl : forall x, env_agree x E E) by (intros x; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0); [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. split; [exact H8|]. split; [exact Hfl|].
  rewrite (rdn_of_bytes1 SEGS _ n (adenot E (SA b off)) bs Lb).
  - f_equal. cbn [edenot]. unfold word_to_le_bytes. rewrite <- Mb, zbytes_map.
    pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z.
  - rewrite (flat_u E _ (Z.of_nat n) Hfl). lia.
  - intros j Hj. rewrite (flat_u E _ (Z.of_nat n) Hfl). rewrite Hst. exact (Rb j Hj).
Qed.

Theorem node_join_zero_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (node_join_zero args).
Proof.
  intros args cs cs' E R FULL model T HC _ Hn Hk. unfold node_join_zero in Hn.
  destruct args as [|b [|[off| | | | | | |] [|[nz| | | | | | |] [|]]]]; try discriminate Hn.
  set (n := Z.to_nat nz) in *.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Ht; [|discriminate] end.
  apply andb_prop in Ht as [Ht Hz]. apply andb_prop in Ht as [Ht Hnz]. apply andb_prop in Ht as [H1 H8].
  apply Nat.leb_le in H1. apply Nat.leb_le in H8. apply Z.eqb_eq in Hnz.
  injection Hn as <-.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (kzero_x_sound0 SEGS E _ (kn cs) (kn cs) b off (ELit nz) HK HK Hz) as (Hm & F1 & F2).
  assert (Hlen : elenZ E (ELit nz) = Z.of_nat n) by (unfold elenZ; cbn [edenot]; rewrite u64_lit by lia; exact Hnz).
  rewrite Hlen in Hm, F2.
  assert (Hfl : flat E (SA b off) (Z.of_nat n)) by (unfold flat; lia).
  set (bs := repeat (Z_to_bv 8 0 : byte) n).
  assert (Lb : length bs = n) by apply repeat_length.
  assert (Mb : map bv_unsigned bs = repeat 0%Z n) by (unfold bs; rewrite map_repeat; reflexivity).
  assert (Hrefl : forall x, env_agree x E E) by (intros x; split; [intros; reflexivity | reflexivity]).
  apply (Hk E R FULL model (conj (Hrefl _) (Hrefl _))); [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0); [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. split; [exact H8|]. split; [exact Hfl|].
  rewrite (rdn_of_bytes1 SEGS _ n (adenot E (SA b off)) bs Lb).
  - f_equal. cbn [edenot]. unfold word_to_le_bytes. rewrite <- Mb, zbytes_map.
    pose proof (bytes_le_to_Z_bound bs) as Bb. rewrite Lb in Bb.
    assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia).
    rewrite u64_lit by lia. rewrite <- Lb. symmetry. apply Z_to_le_bytes_to_Z.
  - rewrite (flat_u E _ (Z.of_nat n) Hfl). lia.
  - intros j Hj. rewrite (flat_u E _ (Z.of_nat n) Hfl).
    apply rdn_one. rewrite (Hm (Z.of_nat j) ltac:(lia)). unfold bs. rewrite nth_repeat. reflexivity.
Qed.
End Sound.
