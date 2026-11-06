(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk MemSplit SymExec3 SymExec3Sound SymRun3.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
Import SX2. Import SX2S.

Lemma u64_lit_small : forall z, (0 <= z < 2 ^ 64)%Z -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. lia. Qed.

Definition LOGWIN : Z := 4096.

Definition entry_out3_b (spi : N) (lo hi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA (EVar i) k) w _ => (N.eqb i spi && (- LOGWIN <=? k)%Z && (k + Z.of_nat w <=? 0)%Z)%bool
  | SE (SA (ELit z) a) w _ => (Z.eqb z 0 && (0 <=? a)%Z && (a + Z.of_nat w <? 2 ^ 64)%Z
                               && ((a + Z.of_nat w <=? lo)%Z || (hi <=? a)%Z))%bool
  | _ => false
  end.
Definition log_out3_b (spi : N) (lo hi : Z) (log : list sentry) : bool := forallb (entry_out3_b spi lo hi) log.

Section Below.
  Variable E : env.
  Variable spi : N.
  Variables lo hi : Z.
  Hypothesis Hsp : (hi <= bv_unsigned (ev E spi) - LOGWIN)%Z.
  Hypothesis Hlo : (0 <= lo <= hi)%Z.

  Lemma mem_denot_out3 : forall base log (x : word),
    log_out3_b spi lo hi log = true ->
    (lo <= bv_unsigned x < hi)%Z ->
    mem_denot E base log x = base x.
  Proof.
    intros base log x Hb Hx. pose proof (u64_range (ev E spi)) as Usp. unfold LOGWIN in *.
    induction log as [|[[b k] w v] rest IH]; [reflexivity|].
    cbn [log_out3_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
    cbn [entry_out3_b] in He. destruct b as [z|i| | | | | |]; try discriminate He.
    - apply andb_prop in He as [He Hm]. apply andb_prop in He as [He H2]. apply andb_prop in He as [H0 H1].
      apply Z.eqb_eq in H0. subst z. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
      cbn [mem_denot]. rewrite wbytes_outside.
      + apply IH. exact Hrest.
      + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot].
        rewrite (u64_lit_small 0), u64_lit_small by lia. lia.
      + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot].
        rewrite (u64_lit_small 0), u64_lit_small by lia.
        apply orb_prop in Hm. destruct Hm as [Hm|Hm]; apply Z.leb_le in Hm; lia.
    - apply andb_prop in He as [He H2]. apply andb_prop in He as [H0 H1].
      apply N.eqb_eq in H0. subst i. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold LOGWIN in *.
      cbn [mem_denot]. rewrite wbytes_outside.
      + apply IH. exact Hrest.
      + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot].
        rewrite u64_lit_small by lia. lia.
      + rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off edenot].
        rewrite u64_lit_small by lia. left. lia.
  Qed.

  Lemma rdn_mem_denot_out3 : forall segs base log (a : word) n,
    log_out3_b spi lo hi log = true ->
    (lo <= bv_unsigned a)%Z -> (bv_unsigned a + Z.of_nat n <= hi)%Z ->
    rdn segs (mem_denot E base log) a n = rdn segs base a n.
  Proof.
    intros segs base log a n Hb Ha1 Ha2. pose proof (u64_range a). pose proof (u64_range (ev E spi)).
    unfold LOGWIN in *.
    apply rdn_ext; [lia|]. intros x Hx. apply mem_denot_out3; [exact Hb | lia].
  Qed.
End Below.

Section Cut.
  Variable spi : N.
  Variables wlo whi : Z.
  Variable abs : list (Z * Z).
  Variable ABSMAX : Z.

  Definition miss_abs_b (a : Z) (n : Z) : bool :=
    forallb (fun iv => (a + n <=? fst iv)%Z || (snd iv <=? a)%Z)%bool abs.

  Definition keep_b (K : kentry) : bool :=
    match K with
    | KWord (SA (EVar i) k) w _ =>
        (N.eqb i spi && (- LOGWIN <=? k)%Z && (k + Z.of_nat w <=? 0)%Z
         && ((k + Z.of_nat w <=? wlo)%Z || (whi <=? k)%Z))%bool
    | KWord (SA (ELit z) a) w _ => (Z.eqb z 0 && (0 <=? a)%Z && (a + Z.of_nat w <=? ABSMAX)%Z && miss_abs_b a (Z.of_nat w))%bool
    | KImg l h => ((0 <=? l)%Z && (h <=? ABSMAX)%Z && miss_abs_b l (h - l))%bool
    | KAlign _ _ => true
    | KRange _ _ _ => true
    | KDisj _ _ _ _ => true
    | KWr _ _ => true
    | _ => false
    end.

  Definition kn_cut3 (kn : list kentry) : list kentry := List.filter keep_b kn.

  Variable segs : list Segment.
  Variable E : env.
  Variables M M' : word -> option byte.
  Hypothesis Hwin : (wlo <= whi <= 0)%Z /\ (- LOGWIN <= wlo)%Z.
  Hypothesis Hsp : (ABSMAX + LOGWIN <= bv_unsigned (ev E spi))%Z /\ (0 <= ABSMAX)%Z.
  Hypothesis Hag : forall x : word,
      ~ (bv_unsigned (ev E spi) + wlo <= bv_unsigned x < bv_unsigned (ev E spi) + whi)%Z ->
      Forall (fun iv => ~ (fst iv <= bv_unsigned x < snd iv)%Z) abs ->
      M' x = M x.
  Hypothesis Hg : mem_grows M M'.
  Hypothesis Habs : Forall (fun iv => (snd iv <= ABSMAX)%Z) abs.

  Lemma miss_abs_sound : forall a n (x : word), miss_abs_b a n = true ->
    (a <= bv_unsigned x < a + n)%Z -> Forall (fun iv => ~ (fst iv <= bv_unsigned x < snd iv)%Z) abs.
  Proof.
    intros a n x Hb Hx. unfold miss_abs_b in Hb. rewrite forallb_forall in Hb. apply Forall_forall.
    intros [lo hi] Hin. specialize (Hb (lo, hi) Hin). cbn [fst snd] in *.
    apply orb_prop in Hb. destruct Hb as [Hb|Hb]; apply Z.leb_le in Hb; lia.
  Qed.

  Lemma above_abs : forall (x : word), (ABSMAX <= bv_unsigned x)%Z ->
    Forall (fun iv => ~ (fst iv <= bv_unsigned x < snd iv)%Z) abs.
  Proof.
    intros x Hx. apply Forall_forall. intros [lo hi] Hin. cbn [fst snd].
    pose proof (proj1 (Forall_forall _ _) Habs (lo, hi) Hin) as Hb. cbn [snd] in Hb. lia.
  Qed.

  Lemma kentry_cut3_sound : forall K, kentry_ok segs E M K -> keep_b K = true -> kentry_ok segs E M' K.
  Proof.
    intros K HK Hb. pose proof (u64_range (ev E spi)) as Usp. destruct Hwin as [W1 W2]. destruct Hsp as [S1 S2].
    destruct K as [[b k] w v|[b k] n|[b k] n bk|l h|e m|e l h|a n|a1 n1 a2 n2]; cbn [keep_b] in Hb;
      cbn [kentry_ok] in HK |- *; try exact HK; try discriminate Hb.
    -
      destruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
      pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
      pose proof Hfl as Hfl'. unfold flat, estart in Hfl'. cbn [a_base a_off] in Hfl'.
      rewrite <- Hr. symmetry. apply rdn_ext; [rewrite Hu; lia|]. intros x Hx. rewrite Hu in Hx. symmetry.
      destruct b as [z|i| | | | | |]; try discriminate Hb.
      +
        apply andb_prop in Hb as [Hb Hm]. apply andb_prop in Hb as [Hb Ha2]. apply andb_prop in Hb as [Hz Ha1].
        apply Z.eqb_eq in Hz. subst z. apply Z.leb_le in Ha1. apply Z.leb_le in Ha2.
        cbn [edenot] in Hu, Hx, Hfl' |- *. rewrite (u64_lit_small 0) in * by lia.
        apply Hag.
        * unfold LOGWIN in *; lia.
        * eapply miss_abs_sound; [exact Hm|]. lia.
      +
        apply andb_prop in Hb as [Hb Hm]. apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
        apply N.eqb_eq in H0. subst i. apply Z.leb_le in H1. apply Z.leb_le in H2. unfold LOGWIN in *.
        cbn [edenot] in Hu, Hx, Hfl' |- *.
        apply Hag.
        * apply orb_prop in Hm. destruct Hm as [Hm|Hm]; apply Z.leb_le in Hm; lia.
        * apply above_abs. unfold LOGWIN in *; lia.
    -
      apply andb_prop in Hb as [Hb Hm]. apply andb_prop in Hb as [H0 H1]. apply Z.leb_le in H0. apply Z.leb_le in H1.
      destruct HK as (HK0 & HK64 & Hnone). split; [exact HK0|]. split; [exact HK64|]. intros i Hi.
      rewrite Hag; [apply Hnone; exact Hi| |].
      + rewrite u64_lit_small by (unfold LOGWIN in *; lia). unfold LOGWIN in *; lia.
      + eapply miss_abs_sound; [exact Hm|]. rewrite u64_lit_small by (unfold LOGWIN in *; lia). lia.
    -
      destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
      eapply store_ok_mono; [exact Hg|]. apply Hst; assumption.
  Qed.

  Theorem know_cut3_sound : forall kn, know_ok segs E M kn -> know_ok segs E M' (kn_cut3 kn).
  Proof.
    intros kn HK. unfold know_ok in *. induction kn as [|K rest IH]; [constructor|].
    apply Forall_cons_iff in HK as [HK1 HK2].
    change (kn_cut3 (K :: rest)) with (if keep_b K then K :: kn_cut3 rest else kn_cut3 rest).
    destruct (keep_b K) eqn:Hb.
    - constructor; [|apply IH; exact HK2]. eapply kentry_cut3_sound; eauto.
    - apply IH. exact HK2.
  Qed.
End Cut.
