(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZAi.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZAi.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QUZl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QUZl. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7S0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7S0.Mq1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfya.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfya. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Ql2m.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Ql2m.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QGeV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QGeV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPiB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPiB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qatc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qatc. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSfG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSfG.Mq2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QhnL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QhnL. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4en.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4en. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QBv7.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QBv7. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q1u2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q1u2.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qy5Y.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qy5Y.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q4J3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q4J3.Mq3. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q3o5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q3o5.Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6q3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6q3.
Import ListNotations. Local Ltac Qfw3_c1.Mq3.model_reg_tac n X mexpr ::= Qfw3_c1.Mq3.mkr__model_reg_tac_1 n X mexpr. Local Ltac Qfw3_c1.Mq3.zeq_fast ::= Qfw3_c1.Mq3.mkr__zeq_fast_0.
Open Scope Z_scope.
Section RC__1. Context {RC__ : Q6q3.RunConsts}.

#[using="Type"] Theorem cmalloc_ctreeI st L BL LS n :
INVL x0 st L BL LS -> (forall c, In c (ld_live L) -> In c (map bslot BL)) -> 0 <= n ->
ctree_ok L (cmalloc (strip st) n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end).
Proof.
intros INV LIVE Hn.
apply (ctree_ok_paths _ L (fun _ _ => True)).
- apply ptree_ctree_ok. eapply (ptree_strel (malloc_control pans0 pupd0 pans0_range st n tt)); [intros; exact I|].
eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range (malloc st n) L _ tt (malloc_INVL st L BL LS n INV Hn)).
- intros L' [cs' r] CP. destruct (cmalloc_leaf_INVL st L BL LS n L' cs' r INV Hn CP) as (LIVE' & st' & LS' & _ & RES).
cbn [snd]. destruct r as [c|]; [| exact I]. destruct RES as (off & _ & _ & NI).
rewrite LIVE'. intros Hc. apply NI. apply LIVE. exact Hc.
Qed.

#[using="Type"] Theorem ccalloc_ctreeI st L BL LS m n :
INVL x0 st L BL LS -> (forall c, In c (ld_live L) -> In c (map bslot BL)) -> 0 <= m -> 0 <= n ->
ctree_ok L (ccalloc (strip st) m n) (fun L' r => match snd r with Some c => ~ In c (ld_live L') | None => True end).
Proof.
intros INV LIVE Hm Hn. unfold ccalloc. destruct (calloc_overflows m n); [exact I|].
apply (cmalloc_ctreeI st L BL LS); [exact INV| exact LIVE| lia].
Qed.

Definition HSIM (s : PState) (L : mled) (LB0 : list block) : Prop :=
exists st BL LS LB1, Permutation LB1 LB0 /\ strip st = ps_m s /\ INVL x0 st L BL LS /\ CORR st LB1 BL.

#[using="Type"] Lemma CORR_slots st LB BL : CORR st LB BL -> map blk_slot LB = map bslot BL.
Proof. induction 1 as [|b k LB' BL' [E _] _ IH]; cbn; [reflexivity| rewrite E, IH; reflexivity]. Qed.

#[using="Type"] Lemma HSIM_live_sub (L : mled) (LB0 : list block) st BL (LB1 : list block) :
Permutation LB1 LB0 -> CORR st LB1 BL -> Permutation (ld_live L) (map blk_slot LB0) ->
forall c, In c (ld_live L) -> In c (map bslot BL).
Proof.
intros P CR PL c Hc. rewrite <- (CORR_slots _ _ _ CR).
pose proof (Permutation_in c PL Hc) as Hc'. apply in_map_iff in Hc' as (b & <- & Hb). apply in_map.
eapply Permutation_in; [apply Permutation_sym; exact P| exact Hb].
Qed.

#[using="Type"] Lemma HSIM_block st LB1 BL (b : block) :
CORR st LB1 BL -> In b LB1 ->
exists off, In ((blk_slot b, off), blk_size b) BL /\ blk_addr b = conc st (blk_slot b) + UNIT * off.
Proof.
intros CR Hb. destruct (Forall2_In_l _ _ _ _ CR Hb) as ([[c off] n] & Hk & (C1 & C2 & C3)).
cbn [bslot boff bsize fst snd] in C1, C2, C3. exists off. rewrite C1, C2. split; [exact Hk| exact C3].
Qed.

#[using="Type"] Lemma HSIM_intro resv {sec} s L LB0 st LBa pbrk st1 L1 BL1 LS1 :
Permutation LBa LB0 -> strip st = ps_m s -> HINV_from resv sec st pbrk LBa ->
strip st1 = ps_m s -> INVL x0 st1 L BL1 LS1 -> (L1 = L) ->
HSIM s L LB0.
Proof.
intros P Est [_ AR] Est1 INV1 ->.
destruct (areach_inv resv st LBa AR) as (L2 & LS2 & BL2 & INV2 & _ & _ & _ & CR).
exists st, BL2, LS2, LBa. split; [exact P|]. split; [exact Est|]. split; [| exact CR].
eapply INVL_transplant; [exact INV2| exact INV1| rewrite Est, Est1; reflexivity].
Qed.

#[using="Type"] Lemma HSIM_set_live s L LB0 v : HSIM s L LB0 -> HSIM s (set_live v L) LB0.
Proof. intros (st & BL & LS & LB1 & P & E & INV & CR). exists st, BL, LS, LB1. auto using INVL_set_live. Qed.

#[using="Type"] Lemma HSIM_perm s L LB0 LB0' : HSIM s L LB0 -> Permutation LB0 LB0' -> HSIM s L LB0'.
Proof.
intros (st & BL & LS & LB1 & P & REST) HP. exists st, BL, LS, LB1. split; [| exact REST].
eapply Permutation_trans; [exact P| exact HP].
Qed.

#[using="Type"] Lemma HSIM_init resv : HSIM (mkPS (strip (minit 0 resv)) 0 tt tt) (led_init resv) [].
Proof.
exists (minit 0 resv), [], (fun _ => []), []. split; [apply Permutation_refl|]. split; [reflexivity|].
split; [apply INVL_init; lia| constructor].
Qed.

#[using="Type"] Lemma HSIM_init_s sec resv : 0 <= sec < 2^64 -> HSIM (mkPS (strip (minit sec resv)) 0 tt tt) (led_init resv) [].
Proof.
intros Hs. exists (minit sec resv), [], (fun _ => []), []. split; [apply Permutation_refl|]. split; [reflexivity|].
split; [apply INVL_init; exact Hs| constructor].
Qed.

End RC__1.
