(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.coturn.FuzzStunClient.images Require Import Asan.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim SeqExec StepTac Hoare.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AsanRegionPoisoned.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VAsanTlsWalk VAsanStackMallocWalk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastV.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVK.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import WalkFastVS.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.gres ::= gres_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.WalkTac.vnorm ::= vnorm_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StepTac.step_simpl ::= step_simpl_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.RefMemcpyLib.not_kept ::= not_kept_fast.
#[local] Ltac OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StartupTac.in_list ::= in_list_fast.
(* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Abbreviation SEGS := Asan.M.loaded_segments.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma zbv_add_nat (x : Z) (j : nat) : (Z_to_bv 64 x + nat_to_word j)%bv = Z_to_bv 64 (x + Z.of_nat j).
Proof.
  unfold nat_to_word. apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned. unfold bv_wrap.
  change (bv_modulus 64) with (2 ^ 64). rewrite <- Z.add_mod by lia. reflexivity.
Qed.

Lemma wbytes_out_any bs m (a x : Z) :
  0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x < 2 ^ 64 ->
  (x < a \/ a + Z.of_nat (length bs) <= x) ->
  wbytes m (Z_to_bv 64 a) bs (Z_to_bv 64 x) = m (Z_to_bv 64 x).
Proof.
  intros Ha Hl Hx [L|R].
  - apply wbytes_below; rewrite !zbv_u by lia; lia.
  - apply wbytes_above; rewrite !zbv_u by lia; lia.
Qed.

Lemma rdn_out_any bs m (a x : Z) (k : nat) :
  0 <= a < 2 ^ 64 -> a + Z.of_nat (length bs) <= 2 ^ 64 -> 0 <= x < 2 ^ 64 -> x + Z.of_nat k <= 2 ^ 64 ->
  (x + Z.of_nat k <= a \/ a + Z.of_nat (length bs) <= x) ->
  rdn SEGS (wbytes m (Z_to_bv 64 a) bs) (Z_to_bv 64 x) k = rdn SEGS m (Z_to_bv 64 x) k.
Proof. intros Ha Hl Hx Hk D. apply rdn_wbytes_out; rewrite !zbv_u by lia; lia. Qed.

(* [comment removed for export] *)
Lemma rdn_hit8_byte m (a : Z) (v : word) (g : Z) :
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= g < 8 ->
  rdn SEGS (wbytes m (Z_to_bv 64 a) (word_to_le_bytes 8 v)) (Z_to_bv 64 (a + g)) 1 = Some [nth (Z.to_nat g) (word_to_le_bytes 8 v) (Z_to_bv 8 0)].
Proof.
  intros Ha H8 Hg.
  pose proof (rdn_wbytes_hit8 SEGS m (Z_to_bv 64 a) v ltac:(rewrite zbv_u by lia; lia)) as R.
  pose proof (rdn_nth SEGS _ 8 (Z_to_bv 64 a) _ (Z.to_nat g) R ltac:(lia)) as B.
  rewrite zbv_add_nat, Z2Nat.id in B by lia. exact B.
Qed.

Definition z8 : list byte := word_to_le_bytes 8 (Z_to_bv 64 0).
Lemma z8_repeat : z8 = repeat (Z_to_bv 8 0) 8.
Proof. reflexivity. Qed.
Lemma length_z8 : length z8 = 8%nat.
Proof. reflexivity. Qed.

Lemma rdn_z8_byte m (a g : Z) :
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= g < 8 ->
  rdn SEGS (wbytes m (Z_to_bv 64 a) z8) (Z_to_bv 64 (a + g)) 1 = Some [Z_to_bv 8 0].
Proof.
  intros Ha H8 Hg. unfold z8. rewrite (rdn_hit8_byte m a (Z_to_bv 64 0) g Ha H8 Hg).
  change (word_to_le_bytes 8 (Z_to_bv 64 0)) with z8. rewrite z8_repeat, nth_repeat. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint offsets (n : nat) : list Z :=
  match n with O => [] | S k => 8 * Z.of_nat n :: offsets k end.

Fixpoint zst (m : word -> option byte) (base : Z) (offs : list Z) : word -> option byte :=
  match offs with
  | [] => wbytes m (Z_to_bv 64 base) z8
  | o :: t => wbytes (zst m base t) (Z_to_bv 64 (base + o)) z8
  end.

Lemma in_offsets n o : In o (offsets n) -> exists k, 1 <= k <= Z.of_nat n /\ o = 8 * k.
Proof.
  induction n as [|n IH]; cbn [offsets In]; [intros []|].
  intros [<-|H]; [exists (Z.of_nat (S n)); lia|]. destruct (IH H) as (k & Hk & ->). exists k. lia.
Qed.

Section ZST.
  Variables (m : word -> option byte) (base : Z) (n : nat).
  Hypothesis Hbase : 0 <= base /\ base + 8 + 8 * Z.of_nat n <= 2 ^ 64.

  #[using="Hbase"] Lemma zst_out_gen offs (y : Z) :
    incl offs (offsets n) -> 0 <= y < 2 ^ 64 -> (y < base \/ base + 8 + 8 * Z.of_nat n <= y) ->
    zst m base offs (Z_to_bv 64 y) = m (Z_to_bv 64 y).
  Proof.
    intros Hin Hy OUT. induction offs as [|o t IH]; cbn [zst].
    - apply wbytes_out_any; rewrite ?length_z8; cbn; lia.
    - destruct (in_offsets n o (Hin o (or_introl eq_refl))) as (k & Hk & ->).
      rewrite wbytes_out_any; rewrite ?length_z8; cbn; try lia. apply IH. intros x Hx. apply Hin. right; exact Hx.
  Qed.

  #[using="Hbase"] Lemma zst_rdn_out_gen offs (a : Z) (k : nat) :
    incl offs (offsets n) -> 0 <= a < 2 ^ 64 -> a + Z.of_nat k <= 2 ^ 64 -> (a + Z.of_nat k <= base \/ base + 8 + 8 * Z.of_nat n <= a) ->
    rdn SEGS (zst m base offs) (Z_to_bv 64 a) k = rdn SEGS m (Z_to_bv 64 a) k.
  Proof.
    intros Hin Ha Hk OUT. induction offs as [|o t IH]; cbn [zst].
    - apply rdn_out_any; rewrite ?length_z8; cbn; lia.
    - destruct (in_offsets n o (Hin o (or_introl eq_refl))) as (j & Hj & ->).
      rewrite rdn_out_any; rewrite ?length_z8; cbn; try lia. apply IH. intros x Hx. apply Hin. right; exact Hx.
  Qed.

  (* [comment removed for export] *)
  #[using="Hbase"] Lemma zst_zero_gen (j : nat) (g : Z) :
    (j <= n)%nat -> 0 <= g < 8 + 8 * Z.of_nat j ->
    rdn SEGS (zst m base (offsets j)) (Z_to_bv 64 (base + g)) 1 = Some [Z_to_bv 8 0].
  Proof.
    revert g. induction j as [|j IH]; intros g Hj Hg; cbn [zst offsets].
    - apply rdn_z8_byte; lia.
    - destruct (Z_lt_le_dec g (8 * Z.of_nat (S j))) as [LT|GE].
      + rewrite rdn_out_any; rewrite ?length_z8; cbn [Z.of_nat]; try lia. apply IH; lia.
      + replace (base + g) with (base + 8 * Z.of_nat (S j) + (g - 8 * Z.of_nat (S j))) by lia. apply rdn_z8_byte; lia.
  Qed.

  #[using="Type"] Lemma zst_keep offs x : m x <> None -> zst m base offs x <> None.
  Proof. induction offs; cbn [zst]; intros; apply wbytes_keep; auto. Qed.
  #[using="Type"] Lemma zst_sok offs x : store_ok SEGS m x 1 = true -> store_ok SEGS (zst m base offs) x 1 = true.
  Proof. induction offs; cbn [zst]; intros; apply store_ok1_wbytes; auto. Qed.
End ZST.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section WRG.
  (* [comment removed for export] *)
  Variables (hoff floff froff sz szm8 : Z) (n : nat).
  (* [comment removed for export] *)
  Variables (usp fs : Z) (hint : word) (m : word -> option byte) (i p : Z).
  Let ffa : Z := fs + froff + sz * p.
  Let fla : Z := fs + floff + p.
  Let sbase : Z := SB + ffa / 8.

  Definition hdr : word -> option byte :=
    wbytes (wbytes (wbytes (wbytes m
      (Z_to_bv 64 (fs + hoff)) (word_to_le_bytes 8 (Z_to_bv 64 (bv_unsigned hint + i + 1))))
      (Z_to_bv 64 (fs + floff + p)) (word_to_le_bytes 1 (Z_to_bv 64 1)))
      (Z_to_bv 64 (fs + froff + sz * p + 24)) (word_to_le_bytes 8 (Z_to_bv 64 usp)))
      (Z_to_bv 64 (fs + froff + sz * p + szm8)) (word_to_le_bytes 8 (Z_to_bv 64 (fs + floff + p))).
  Definition WRG : word -> option byte := zst hdr (SB + (fs + froff + sz * p) / 8) (offsets n).

  Hypothesis Hsz : sz = 64 * (1 + Z.of_nat n) /\ szm8 = sz - 8.
  Hypothesis Hh : 0 <= hoff /\ hoff + 8 <= floff.
  Hypothesis Hfl : 0 <= p /\ floff + p < froff.
  (* [comment removed for export] *)
  Hypothesis Hfs : 0 <= fs /\ (ffa + sz <= 0x7fff7000 \/ 0x10007fff8000 <= fs) /\ ffa + sz <= 2 ^ 47.
  Hypothesis Husp : 0 <= usp < 2 ^ 64.

  #[using="hoff floff szm8 fla sbase Hsz Hh Hfl Hfs"] Lemma ffa_facts : fs + froff <= ffa /\ 0 <= ffa / 8 /\ SB + ffa / 8 + sz / 8 <= 0x10007fff8000 /\ sz / 8 = 8 + 8 * Z.of_nat n /\ 64 <= sz.
  Proof.
    pose proof SB_val. destruct Hsz as [S1 S2]. unfold ffa in *.
    assert (0 <= sz * p) by nia.
    pose proof (Z.div_pos (fs + froff + sz * p) 8 ltac:(lia) ltac:(lia)).
    pose proof (Z.div_le_upper_bound (fs + froff + sz * p) 8 (2 ^ 44 - 8 * (1 + Z.of_nat n)) ltac:(lia) ltac:(lia)).
    assert (E : sz / 8 = 8 + 8 * Z.of_nat n) by (rewrite S1; replace (64 * (1 + Z.of_nat n)) with ((8 + 8 * Z.of_nat n) * 8) by lia; apply Z.div_mul; lia).
    lia.
  Qed.

  (* [comment removed for export] *)
  #[using="sbase Hsz Hh Hfl Hfs"] Lemma WRG_out (y : Z) :
    0 <= y < 2 ^ 64 ->
    ~ ((fs + hoff <= y < fs + hoff + 8) \/ y = fla \/ (ffa + 24 <= y < ffa + 32) \/ (ffa + szm8 <= y < ffa + sz)
       \/ (SB + ffa / 8 <= y < SB + ffa / 8 + sz / 8)) ->
    WRG (Z_to_bv 64 y) = m (Z_to_bv 64 y).
  Proof.
    intros Hy NB. pose proof ffa_facts as (A1 & A2 & A3 & A4 & A5). pose proof SB_val. unfold WRG. fold ffa.
    rewrite (zst_out_gen hdr (SB + ffa / 8) n ltac:((ltac2:(LK.k [@Hsz; @Hh; @Hfl; @Hfs; @NB; @A2; @A3; @A4; @A5; @H]); lia)) (offsets n) y ltac:(intros o Ho; exact Ho) Hy ltac:((ltac2:(LK.k [@Hsz; @Hh; @Hfl; @Hfs; @NB; @A2; @A3; @A4; @A5; @H]); lia))).
    unfold hdr. fold ffa. unfold fla in NB.
    rewrite !wbytes_out_any; rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try (ltac2:(LK.k [@Hsz; @Hh; @Hfl; @Hfs; @Hy; @NB; @A2; @A3; @A4; @A5; @H]); lia). reflexivity.
  Qed.

  Ltac peel := rewrite rdn_out_any; rewrite ?length_N_to_le_bytes; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; try lia.

  #[using="ffa sbase Hsz Hh Hfl Hfs"] Lemma WRG_flag : rdn SEGS WRG (Z_to_bv 64 fla) 1 = Some [Z_to_bv 8 1].
  Proof.
    pose proof ffa_facts as (A1 & A2 & A3 & A4 & A5). pose proof SB_val. unfold WRG. fold ffa.
    rewrite (zst_rdn_out_gen hdr (SB + ffa / 8) n ltac:(lia) (offsets n) fla 1 ltac:(intros o Ho; exact Ho)); try (unfold fla; cbn; lia).
    unfold hdr, fla. fold ffa. peel. peel.
    apply (rdn_wbytes_hit SEGS (word_to_le_bytes 1 (Z_to_bv 64 1))). rewrite zbv_u; cbn; lia.
  Qed.

  #[using="fla sbase Hsz Hh Hfl Hfs"] Lemma WRG_24 : rdn SEGS WRG (Z_to_bv 64 (ffa + 24)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 usp)).
  Proof.
    pose proof ffa_facts as (A1 & A2 & A3 & A4 & A5). pose proof SB_val. unfold WRG. fold ffa.
    rewrite (zst_rdn_out_gen hdr (SB + ffa / 8) n ltac:((ltac2:(LK.k [@Hh; @Hfl; @A2; @A3; @A4; @A5; @H; @Hfs]); lia)) (offsets n) (ffa + 24) 8 ltac:(intros o Ho; exact Ho)); try (cbn; (ltac2:(LK.k [@Hh; @Hfl; @A2; @A3; @A4; @A5; @H; @Hfs]); lia)).
    unfold hdr. fold ffa. peel. apply rdn_wbytes_hit8. rewrite zbv_u; lia.
  Qed.

  #[using="sbase Hsz Hh Hfl Hfs"] Lemma WRG_sz : rdn SEGS WRG (Z_to_bv 64 (ffa + szm8)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 fla)).
  Proof.
    pose proof ffa_facts as (A1 & A2 & A3 & A4 & A5). pose proof SB_val. unfold WRG. fold ffa.
    rewrite (zst_rdn_out_gen hdr (SB + ffa / 8) n ltac:((ltac2:(LK.k [@Hh; @Hfl; @A2; @A3; @A4; @A5; @H; @Hsz; @Hfs]); lia)) (offsets n) (ffa + szm8) 8 ltac:(intros o Ho; exact Ho)); try (cbn; (ltac2:(LK.k [@Hh; @Hfl; @A2; @A3; @A4; @A5; @H; @Hsz; @Hfs]); lia)).
    unfold hdr. fold ffa fla. apply rdn_wbytes_hit8. rewrite zbv_u; lia.
  Qed.

  #[using="fla sbase Hsz Hh Hfl Hfs"] Lemma WRG_zero (g : Z) : 0 <= g < sz / 8 -> rdn SEGS WRG (Z_to_bv 64 (SB + ffa / 8 + g)) 1 = Some [Z_to_bv 8 0].
  Proof.
    intros Hg. pose proof ffa_facts as (A1 & A2 & A3 & A4 & A5). pose proof SB_val. unfold WRG. fold ffa.
    apply (zst_zero_gen hdr (SB + ffa / 8) n ltac:(lia) n g (le_n n)). lia.
  Qed.

  #[using="Type"] Lemma WRG_keep x : m x <> None -> WRG x <> None.
  Proof. intros Hx. unfold WRG. apply zst_keep. unfold hdr. repeat apply wbytes_keep. exact Hx. Qed.
  #[using="Type"] Lemma WRG_sok x : store_ok SEGS m x 1 = true -> store_ok SEGS WRG x 1 = true.
  Proof. intros Hx. unfold WRG. apply zst_sok. unfold hdr. repeat apply store_ok1_wbytes. exact Hx. Qed.
End WRG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma WR0_eq usp fs hint m i p : WR usp fs hint m i p = WRG 0 4096 36864 64 56 0 usp fs hint m i p.
Proof. unfold WR, WRG, hdr, ff, FL0, FR0. cbn [zst offsets]. rewrite Z.add_0_r. reflexivity. Qed.
Lemma WR1_eq usp fs hint m i p : WR1 usp fs hint m i p = WRG 8 20480 1085440 128 120 1 usp fs hint m i p.
Proof. unfold WR1, WRG, hdr, ff1, FL1, FR1. cbn [zst offsets Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]. reflexivity. Qed.
Lemma WR2_eq usp fs hint m i p : WR2 usp fs hint m i p = WRG 16 28672 2134016 256 248 3 usp fs hint m i p.
Proof. unfold WR2, WRG, hdr, ff2, FL2, FR2. cbn [zst offsets Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]. reflexivity. Qed.
Lemma WR3_eq usp fs hint m i p : WR3 usp fs hint m i p = WRG 24 32768 3182592 512 504 7 usp fs hint m i p.
Proof. unfold WR3, WRG, hdr, ff3, FL3, FR3. cbn [zst offsets Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]. reflexivity. Qed.
Lemma WR4_eq usp fs hint m i p : WR4 usp fs hint m i p = WRG 32 34816 4231168 1024 1016 15 usp fs hint m i p.
Proof. unfold WR4, WRG, hdr, ff4, FL4, FR4. cbn [zst offsets Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Pos.mul]. reflexivity. Qed.
