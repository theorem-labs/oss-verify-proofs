(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BCatExec BCatSim BSeqExec BStoreOk BSimInv BExitSim BShapeAlg BSymExec BSymExec2 BSymExec2Sound BSymRun BSymDrive BSymDriveX BMemSplit.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma low32_zero_sext : low32 (Z_to_bv 64 0) = sext 32 (0 : bv 12).
Proof. apply bv_eq. reflexivity. Qed.

Lemma edenot_addw0_r : forall E a,
  (bv_unsigned (edenot E a) < 2 ^ 31)%Z ->
  edenot E (EAluw ALU_ADD a (ELit 0)) = edenot E a.
Proof.
  intros E a Ha. cbn [edenot]. rewrite low32_zero_sext, w_addiw.
  change (bv_signed (0 : bv 12)) with 0%Z. apply v_addiw_id. exact Ha.
Qed.

Lemma alu32_add_comm : forall x y : bv 32, alu32 ALU_ADD x y = alu32 ALU_ADD y x.
Proof.
  intros x y. change (x + y = y + x). apply bv_eq.
  rewrite !bv_add_unsigned. f_equal. lia.
Qed.

Lemma edenot_addw0_l : forall E a,
  (bv_unsigned (edenot E a) < 2 ^ 31)%Z ->
  edenot E (EAluw ALU_ADD (ELit 0) a) = edenot E a.
Proof.
  intros E a Ha. cbn [edenot]. rewrite alu32_add_comm.
  pose proof (edenot_addw0_r E a Ha) as H. cbn [edenot] in H. exact H.
Qed.

Lemma edenot_exts4 : forall E a,
  (bv_unsigned (edenot E a) < 2 ^ 31)%Z ->
  edenot E (EExt true 0 4 a) = edenot E a.
Proof.
  intros E a Ha. cbn [edenot]. apply ext_val_sx_id; [lia|].
  change (2 ^ (8 * Z.of_nat 4 - 1))%Z with (2 ^ 31)%Z. exact Ha.
Qed.

Ltac intisms E e Hsmall :=
  repeat first [ rewrite (edenot_addw0_r E e Hsmall)
               | rewrite (edenot_addw0_l E e Hsmall)
               | rewrite (edenot_exts4 E e Hsmall) ].

Definition win_out_b (spi : nat) (lo hi ihi : Z) (b : expr) (k n : Z) : bool :=
  match b with
  | EVar i => Nat.eqb i spi && (Z.leb (k + n) lo || Z.leb hi k)
              && Z.leb (- 2 ^ 40) k && Z.leb (k + n) (2 ^ 40) && Z.leb 0 n
  | ELit z => Z.eqb z 0 && Z.leb 0 k && Z.leb 0 n && Z.leb (k + n) ihi
  | _ => false
  end.

Definition win_ok (E : env) (spi : nat) (lo hi ihi : Z) : Prop :=
  (2 ^ 41 <= bv_unsigned (ev E spi))%Z /\ (bv_unsigned (ev E spi) + 2 ^ 41 <= 2 ^ 64)%Z
  /\ (lo <= hi)%Z /\ (- 2 ^ 40 <= lo)%Z /\ (hi <= 2 ^ 40)%Z
  /\ (0 <= ihi)%Z /\ (ihi <= bv_unsigned (ev E spi) + lo)%Z.

Lemma win_out_sound : forall E spi lo hi ihi b k n,
  win_out_b spi lo hi ihi b k n = true -> win_ok E spi lo hi ihi ->
  (0 <= bv_unsigned (edenot E b) + k)%Z
  /\ (bv_unsigned (edenot E b) + k < 2 ^ 64 /\ bv_unsigned (edenot E b) + k + n <= 2 ^ 64)%Z
  /\ (0 <= n)%Z
  /\ forall x : word,
       (bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + n)%Z ->
       ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z.
Proof.
  intros E spi lo hi ihi b k n Hb (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate.
  - repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
    apply Z.eqb_eq in Hb. subst z.
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
    cbn [edenot]. change (bv_unsigned (Z_to_bv 64 0)) with 0%Z.
    repeat split; try lia.
  - repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]).
    apply Nat.eqb_eq in Hb. subst i.
    repeat match goal with
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : (_ || _)%bool = true |- _ => apply orb_prop in H
           end.
    cbn [edenot]. repeat split; try lia.
Qed.

Definition entry_out_b (spi : nat) (lo hi ihi : Z) (e : sentry) : bool :=
  match e with
  | SE (SA b k) w _ => win_out_b spi lo hi ihi b k (Z.of_nat w)
  end.

Definition log_out_b (spi : nat) (lo hi ihi : Z) (log : list sentry) : bool :=
  forallb (entry_out_b spi lo hi ihi) log.

Lemma mem_denot_out : forall E M log spi lo hi ihi (x : word),
  log_out_b spi lo hi ihi log = true -> win_ok E spi lo hi ihi ->
  (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
  mem_denot E M log x = M x.
Proof.
  intros E M log spi lo hi ihi x Hb Hw Hx.
  induction log as [|[[b k] w v] rest IH]; [reflexivity|].
  cbn [log_out_b forallb] in Hb. apply andb_prop in Hb as [He Hrest].
  cbn [entry_out_b] in He.
  destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) He Hw) as (A & B & C & D).
  cbn [mem_denot]. rewrite wbytes_outside.
  - apply IH. exact Hrest.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia. lia.
  - rewrite length_N_to_le_bytes. unfold adenot, v_addi. cbn [a_base a_off]. rewrite u_small by lia.
    pose proof (u64_range x).
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k)) as [L|G]; [left; lia|].
    destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned (edenot E b) + k + Z.of_nat w)) as [L2|G2]; [|right; lia].
    exfalso. apply (D x); lia.
Qed.

Lemma rdn_mem_denot_out : forall segs E M log spi lo hi ihi (a : word) n,
  log_out_b spi lo hi ihi log = true -> win_ok E spi lo hi ihi ->
  (bv_unsigned (ev E spi) + lo <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat n <= bv_unsigned (ev E spi) + hi)%Z ->
  rdn segs (mem_denot E M log) a n = rdn segs M a n.
Proof.
  intros segs E M log spi lo hi ihi a n Hb Hw H1 H2.
  destruct Hw as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  apply rdn_agree. intros j Hj. pose proof (u64_range a).
  apply (mem_denot_out E M log spi lo hi ihi); [exact Hb | repeat split; assumption |].
  rewrite u_small by lia. lia.
Qed.

Definition kentry_out_b (spi : nat) (lo hi ihi : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA b k) w _ => win_out_b spi lo hi ihi b k (Z.of_nat w)
  | KZero (SA b k) (ELit n) => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
  | KBlob (SA b k) (ELit n) _ => Z.ltb n (2 ^ 64) && win_out_b spi lo hi ihi b k n
  | KImg l h => Z.leb h ihi
  | KAlign _ _ => true
  | KRange _ _ _ => true
  | KDisj _ _ _ _ => true
  | KWr _ _ => true
  | _ => false
  end.

Definition kn_cut (spi : nat) (lo hi ihi : Z) (kn : list kentry) : list kentry :=
  List.filter (kentry_out_b spi lo hi ihi) kn.

Lemma elenZ_lit_small : forall E n, (0 <= n < 2 ^ 64)%Z -> elenZ E (ELit n) = n.
Proof. intros E n Hn. unfold elenZ. cbn [edenot]. apply u_small. lia. Qed.

Lemma kentry_cut_sound : forall segs E M M' spi lo hi ihi K,
  win_ok E spi lo hi ihi ->
  (forall x : word,
     ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z -> M' x = M x) ->
  mem_grows M M' ->
  kentry_ok segs E M K -> kentry_out_b spi lo hi ihi K = true -> kentry_ok segs E M' K.
Proof.
  intros segs E M M' spi lo hi ihi K Hw Hag Hg HK Hb.
  pose proof Hw as Hw'. destruct Hw' as (W1 & W2 & W3 & W4 & W5 & W6 & W7).
  destruct K as [[b k] w v|[b k] n|[b k] n bk|l h|e m|e l h|a n|a1 n1 a2 n2]; cbn [kentry_out_b] in Hb;
    cbn [kentry_ok] in HK |- *; try exact HK.
  -
    destruct HK as (Hw8 & Hfl & Hr). split; [exact Hw8|]. split; [exact Hfl|].
    destruct (win_out_sound E spi lo hi ihi b k (Z.of_nat w) Hb Hw) as (A & B & C & D).
    rewrite <- Hr. apply rdn_agree. intros j Hj. apply Hag.
    pose proof (flat_u E _ _ Hfl) as Hu. unfold estart in Hu. cbn [a_base a_off] in Hu.
    rewrite Hu. apply D. rewrite u_small by lia. lia.
  -
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hz).
    assert (Hn0 : (0 <= n)%Z).
    { destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
        repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
        repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia. }
    rewrite elenZ_lit_small in Hfl, Hz |- * by lia.
    split; [exact Hfl|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
    rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
    apply D. rewrite u_small by lia. lia.
  -
    destruct n as [n| | | | | | |]; try discriminate. apply andb_prop in Hb as [Hn Hb]. apply Z.ltb_lt in Hn.
    destruct HK as (Hfl & Hlen & Hz).
    assert (Hn0 : (0 <= n)%Z).
    { destruct b as [z|i| | | | | |]; cbn [win_out_b] in Hb; try discriminate;
        repeat (apply andb_prop in Hb; destruct Hb as [Hb ?]);
        repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end; lia. }
    rewrite elenZ_lit_small in Hfl, Hlen, Hz |- * by lia.
    split; [exact Hfl|]. split; [exact Hlen|]. intros i Hi.
    destruct (win_out_sound E spi lo hi ihi b k n Hb Hw) as (A & B & C & D).
    rewrite Hag; [apply Hz; exact Hi|]. unfold estart. cbn [a_base a_off].
    apply D. rewrite u_small by lia. lia.
  -
    apply Z.leb_le in Hb. destruct HK as (H0 & H64 & Hnone).
    split; [exact H0|]. split; [exact H64|]. intros i Hi.
    rewrite Hag; [apply Hnone; exact Hi|]. rewrite u_small by lia. lia.
  -
    destruct HK as [Hfl Hst]. split; [exact Hfl|]. intros d m Hd Hm.
    eapply store_ok_mono; [exact Hg|]. apply Hst; assumption.
Qed.

Theorem know_cut_sound : forall segs E M M' spi lo hi ihi kn,
  win_ok E spi lo hi ihi ->
  (forall x : word,
     ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z -> M' x = M x) ->
  mem_grows M M' ->
  know_ok segs E M kn -> know_ok segs E M' (kn_cut spi lo hi ihi kn).
Proof.
  intros segs E M M' spi lo hi ihi kn Hw Hag Hg HK. unfold know_ok in *.
  induction kn as [|K rest IH]; [constructor|].
  apply Forall_cons_iff in HK as [HK1 HK2].
  change (kn_cut spi lo hi ihi (K :: rest))
    with (if kentry_out_b spi lo hi ihi K then K :: kn_cut spi lo hi ihi rest else kn_cut spi lo hi ihi rest).
  destruct (kentry_out_b spi lo hi ihi K) eqn:Hb.
  - constructor; [|apply IH; exact HK2]. eapply kentry_cut_sound; eauto.
  - apply IH. exact HK2.
Qed.

Lemma wbytes_agree_out : forall M (a : word) bs E spi lo hi,
  (bv_unsigned (ev E spi) + lo <= bv_unsigned a)%Z ->
  (bv_unsigned a + Z.of_nat (length bs) <= bv_unsigned (ev E spi) + hi)%Z ->
  (bv_unsigned (ev E spi) + hi <= 2 ^ 64)%Z ->
  forall x : word,
    ~ (bv_unsigned (ev E spi) + lo <= bv_unsigned x < bv_unsigned (ev E spi) + hi)%Z ->
    wbytes M a bs x = M x.
Proof.
  intros M a bs E spi lo hi H1 H2 H3 x Hx. pose proof (u64_range x).
  apply wbytes_outside; [lia|].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a)) as [L|G]; [left; exact L | right].
  destruct (Z.lt_ge_cases (bv_unsigned x) (bv_unsigned a + Z.of_nat (length bs))) as [L2|G2]; [|exact G2].
  exfalso. apply Hx. lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
