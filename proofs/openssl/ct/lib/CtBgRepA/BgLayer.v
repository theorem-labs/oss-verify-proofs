(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Arr. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prog BnBase BnModel BnTree BnInv BgState BgInv.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require BgSpecs.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnW Require Import BnMem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout RT_iface RT_client_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnP Require BnKit2.
From OssFuzzTheorems.Proofs.openssl.ct.lib.BnAsan Require Import AsKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtKitA Require Import LibKitA ARun BnHeapA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBgRepA Require ApBnRepA.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBgRepA Require Import BgRepDefs BgRep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeiling1. Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation SP0 := (@ar_SP0 AR).
Local Notation LIBW_cs := (@ar_LIBW_cs AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Definition cx_fp (s : ST) (OW : list block) (PL : placement) (x : Z) : Prop :=
  (exists ac qc, pl_ctx PL = Some (ac, qc) /\ ac <= x < ac + BN_CTX_SZ)
  \/ (exists q H, In q (gx_items (st_ctx s)) /\ In (q, H, ITEM_SZ) OW /\ H + 384 <= x < H + 400)
  \/ (exists q I, gx_indexes (st_ctx s) = Some q /\ In (q, I, FRAMES_SZ) OW /\ I <= x < I + FRAMES_SZ).

(* [comment removed for export] *)
Definition mont_fp (PL : placement) (x : Z) : Prop :=
  (exists am qm, pl_mont PL = Some (am, qm) /\ am + 72 <= x < am + MONT_CTX_SZ)
  \/ (exists c, pl_recp PL = Some c /\ c <= x < c + RECP_SC_SZ).

(* [comment removed for export] *)
Definition own_fpc (cxo : bool) (hs : list bnref) (s : ST) (OW : list block) (PL : placement) (EA : ApBnRepA.err_addrs) (x : Z) : Prop :=
  libw x
  \/ (exists r a, ref_at s OW PL r a /\ vref r s /\ ~ In r hs /\ bn_fp OW (pl_of PL r) a (getbn r s) x)
  \/ (cxo = false /\ cx_fp s OW PL x)
  \/ mont_fp PL x
  \/ ApBnRepA.err_fp OW EA x.

Lemma libw_bn : forall a, ApBnRepA.libw a -> libw a.
Proof. intros a H. unfold libw, LIBW_bgr. apply rin_ivs_app. left. exact H. Qed.

Lemma libw_const_one : forall a, CONST_ONE <= a < CONST_ONE + BN_STRUCT_SZ -> libw a.
Proof. intros a H. unfold libw, LIBW_bgr. apply rin_ivs_app. right. cbn. lia. Qed.

(* [comment removed for export] *)

Lemma libw_cases : forall a, libw a <-> ApBnRepA.libw a \/ CONST_ONE <= a < CONST_ONE + BN_STRUCT_SZ.
Proof.
  intros a. unfold libw, LIBW_bgr, ApBnRepA.libw. rewrite rin_ivs_app. cbn [rin_ivs fst snd]. tauto.
Qed.

(* [comment removed for export] *)

Lemma lib_cells_agree : forall (P : Z -> Prop) m m', agree_on P m m' -> (forall a, ApBnRepA.libw a -> P a) -> (forall a, libw a -> P a) -> lib_cells m -> lib_cells m'.
Proof.
  intros P m m' AG HL HL' [H1 H2]. split; [eapply ApBnRepA.ossl_exit_cells_agree; eauto| exact I].
Qed.

(* [comment removed for export] *)
Lemma ref_at_item_slot : forall s OW PL k q H j,
  nth_error (gx_items (st_ctx s)) k = Some q -> In (q, H, ITEM_SZ) OW -> (j < BN_CTX_POOL_SIZE)%nat ->
  ref_at s OW PL (RPool (BN_CTX_POOL_SIZE * k + j)) (H + 24 * Z.of_nat j).
Proof.
  intros s OW PL k q H j Hk Hin Hj. apply ref_at_pool. exists q, H.
  rewrite Nat.mul_comm, Nat.div_add_l, Nat.div_small, Nat.add_0_r by (unfold BN_CTX_POOL_SIZE in *; lia).
  split; [exact Hk|]. split; [exact Hin|]. f_equal. f_equal.
  rewrite Nat.add_comm, Nat.Div0.mod_add, Nat.mod_small by (unfold BN_CTX_POOL_SIZE in *; lia). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma gen_transport : forall P (R R' : bnR) cxo s m m' OW OW' PL,
  bn_mem_gen R cxo s m OW PL -> agree_on P m m' ->
  (cxo = false -> forall x, cx_fp s OW PL x -> P x) ->
  (forall ac qc, pl_ctx PL = Some (ac, qc) -> In (qc, ac, BN_CTX_SZ) OW -> In (qc, ac, BN_CTX_SZ) OW') ->
  (forall q H, In q (gx_items (st_ctx s)) -> In (q, H, ITEM_SZ) OW -> In (q, H, ITEM_SZ) OW') ->
  (forall q I, gx_indexes (st_ctx s) = Some q -> In (q, I, FRAMES_SZ) OW -> In (q, I, FRAMES_SZ) OW') ->
  (forall am qm, pl_mont PL = Some (am, qm) -> In (qm, am, MONT_CTX_SZ) OW -> In (qm, am, MONT_CTX_SZ) OW') ->
  (forall r p, (r < NFIX)%nat -> pl_of PL r = Some p -> place_ok OW p -> place_ok OW' p) ->
  (forall x, mont_fp PL x -> P x) ->
  (forall r a, ref_at s OW PL r a -> R a (getbn r s) r -> R' a (getbn r s) r) ->
  bn_mem_gen R' cxo s m' OW' PL.
Proof.
  intros P R R' cxo s m m' OW OW' PL HG AG HCx HOc HOi HOx HOm HPL HMf HR.
  pose proof HG as (HF & HN & HC & HM).
  split.
  { intros r p Hr E. destruct (HF r p Hr E) as [OK H]. split; [eapply HPL; eauto|].
    apply HR; [|exact H]. apply ref_at_fixed; [exact Hr|]. exists p. auto. }
  split; [exact HN|]. split.
  - destruct (pl_ctx PL) as [[ac qc]|] eqn:Ec; [|exact HC]. destruct HC as (Hinc & Hs & Ix & LHs & HCe & HIT).
    split; [apply HOc; [reflexivity| exact Hinc]|]. exists Hs, Ix. split; [exact LHs|]. split.
    + intros Ecx. destruct (HCe Ecx) as [HCe1 HSt]. split.
      * eapply rw_cells_agree; [exact AG| exact HCe1|]. intros x Hx. apply (HCx Ecx). left. exists ac, qc. cbn in Hx. unfold BN_CTX_SZ. split; [exact Ec| lia].
      * unfold stack_rep in *. destruct (gx_indexes (st_ctx s)) as [q|] eqn:Eq; [|exact HSt].
        destruct HSt as (Hin & Hsz & stale & Hlen & Harr). split; [apply HOx; [reflexivity| exact Hin]|]. split; [exact Hsz|]. exists stale. split; [exact Hlen|].
        eapply LibKitA.u32arr_agree; [exact AG| exact Harr|]. intros x Hx. apply (HCx Ecx). right; right. exists q, Ix.
        rewrite length_app, length_map in Hx. split; [exact Eq|]. split; [exact Hin|]. unfold FRAMES_SZ, BN_CTX_START_FRAMES in *. lia.
    + assert (HIT' : items_gen R' cxo m OW (gx_items (st_ctx s)) Hs (skipn NFIX (st_bns s)) 0 0).
      { eapply items_gen_impl_idx; [|exact HIT]. intros k q H j Hk HH Hj HRk. rewrite Nat.add_0_l in *.
        destruct (items_gen_nth _ _ _ _ _ _ _ _ _ _ _ HIT Hk) as (H' & HH' & Hin & _). rewrite HH in HH'. injection HH' as <-.
        pose proof (HR (RPool (BN_CTX_POOL_SIZE * k + j)) (H + 24 * Z.of_nat j) (ref_at_item_slot s OW PL k q H j Hk Hin Hj)) as X.
        rewrite getbn_pool in X. apply X. exact HRk. }
      eapply (items_gen_transport P R' R'); [exact HIT'| exact AG|].
      intros q H Hq Hin. split; [apply HOi; assumption|]. intros Ecx x Hx. apply (HCx Ecx). right; left. exists q, H. auto.
  - destruct HM as [HMo HRc]. split.
    + destruct (pl_mont PL) as [[am qm]|] eqn:Em; [|exact I]. destruct HMo as [Hin Hce]. split; [apply HOm; [reflexivity| exact Hin]|].
      eapply rw_cells_agree; [exact AG| exact Hce|]. intros x Hx. apply HMf. left. exists am, qm.
      cbn in Hx. unfold MONT_CTX_SZ. split; [exact Em| lia].
    + destruct (pl_recp PL) as [c|] eqn:Er; [|exact I].
      eapply rw_cells_agree; [exact AG| exact HRc|]. intros x Hx. apply HMf. right. exists c.
      cbn in Hx. unfold RECP_SC_SZ. split; [exact Er| lia].
Qed.

(* [comment removed for export] *)
Lemma gen_transport2 : forall P (R R' : bnR) cxo s0 s m m' OW OW' PL,
  bn_mem_gen R cxo s0 m OW PL -> agree_on P m m' ->
  st_bns s = st_bns s0 -> st_ctx s = st_ctx s0 ->
  (cxo = false -> forall x, cx_fp s0 OW PL x -> P x) ->
  (forall ac qc, pl_ctx PL = Some (ac, qc) -> In (qc, ac, BN_CTX_SZ) OW -> In (qc, ac, BN_CTX_SZ) OW') ->
  (forall q H, In q (gx_items (st_ctx s0)) -> In (q, H, ITEM_SZ) OW -> In (q, H, ITEM_SZ) OW') ->
  (forall q I, gx_indexes (st_ctx s0) = Some q -> In (q, I, FRAMES_SZ) OW -> In (q, I, FRAMES_SZ) OW') ->
  (forall am qm, pl_mont PL = Some (am, qm) -> In (qm, am, MONT_CTX_SZ) OW -> In (qm, am, MONT_CTX_SZ) OW') ->
  (forall r p, (r < NFIX)%nat -> pl_of PL r = Some p -> place_ok OW p -> place_ok OW' p) ->
  match pl_mont PL with
  | Some (am, qm) => (mont_cells s = mont_cells s0 /\ forall x, am + 72 <= x < am + MONT_CTX_SZ -> P x) \/ rw_cells ctasegs m' (am + 72) (mont_cells s)
  | None => True end ->
  match pl_recp PL with
  | Some c => (recp_cells s = recp_cells s0 /\ forall x, c <= x < c + RECP_SC_SZ -> P x) \/ rw_cells ctasegs m' c (recp_cells s)
  | None => True end ->
  (forall r a, ref_at s0 OW PL r a -> R a (getbn r s0) r -> R' a (getbn r s0) r) ->
  bn_mem_gen R' cxo s m' OW' PL.
Proof.
  intros P R R' cxo s0 s m m' OW OW' PL HG AG EB ECX HCx HOc HOi HOx HOm HPL HMo' HRc' HR.
  pose proof HG as (HF & HN & HC & [HMo HRc]).
  assert (EG : forall r, getbn r s = getbn r s0) by (intros r; unfold getbn; rewrite EB; reflexivity).
  split.
  { intros r p Hr E. destruct (HF r p Hr E) as [OK H]. split; [eapply HPL; eauto|]. rewrite EG.
    apply HR; [|exact H]. apply ref_at_fixed; [exact Hr|]. exists p. auto. }
  split; [intros r Hr E; rewrite EG; apply HN; assumption|]. rewrite ECX, EB. split.
  - destruct (pl_ctx PL) as [[ac qc]|] eqn:Ec; [|exact HC]. destruct HC as (Hinc & Hs & Ix & LHs & HCe & HIT).
    split; [apply HOc; [reflexivity| exact Hinc]|]. exists Hs, Ix. split; [exact LHs|]. split.
    + intros Ecx. destruct (HCe Ecx) as [HCe1 HSt]. split.
      * eapply rw_cells_agree; [exact AG| exact HCe1|]. intros x Hx. apply (HCx Ecx). left. exists ac, qc. cbn in Hx. unfold BN_CTX_SZ. split; [exact Ec| lia].
      * unfold stack_rep in *. destruct (gx_indexes (st_ctx s0)) as [q|] eqn:Eq; [|exact HSt].
        destruct HSt as (Hin & Hsz & stale & Hlen & Harr). split; [apply HOx; [reflexivity| exact Hin]|]. split; [exact Hsz|]. exists stale. split; [exact Hlen|].
        eapply LibKitA.u32arr_agree; [exact AG| exact Harr|]. intros x Hx. apply (HCx Ecx). right; right. exists q, Ix.
        rewrite length_app, length_map in Hx. split; [exact Eq|]. split; [exact Hin|]. unfold FRAMES_SZ, BN_CTX_START_FRAMES in *. lia.
    + assert (HIT' : items_gen R' cxo m OW (gx_items (st_ctx s0)) Hs (skipn NFIX (st_bns s0)) 0 0).
      { eapply items_gen_impl_idx; [|exact HIT]. intros k q H j Hk HH Hj HRk. rewrite Nat.add_0_l in *.
        destruct (items_gen_nth _ _ _ _ _ _ _ _ _ _ _ HIT Hk) as (H' & HH' & Hin & _). rewrite HH in HH'. injection HH' as <-.
        pose proof (HR (RPool (BN_CTX_POOL_SIZE * k + j)) (H + 24 * Z.of_nat j) (ref_at_item_slot s0 OW PL k q H j Hk Hin Hj)) as X.
        rewrite getbn_pool in X. apply X. exact HRk. }
      eapply (items_gen_transport P R' R'); [exact HIT'| exact AG|].
      intros q H Hq Hin. split; [apply HOi; assumption|]. intros Ecx x Hx. apply (HCx Ecx). right; left. exists q, H. auto.
  - split.
    + destruct (pl_mont PL) as [[am qm]|] eqn:Em; [|exact I]. destruct HMo as [Hin Hce]. split; [apply HOm; [reflexivity| exact Hin]|].
      destruct HMo' as [[EMC HP]|NEW]; [|exact NEW]. rewrite EMC.
      eapply rw_cells_agree; [exact AG| exact Hce|]. intros x Hx. apply HP. cbn in Hx. unfold MONT_CTX_SZ. lia.
    + destruct (pl_recp PL) as [c|] eqn:Er; [|exact I].
      destruct HRc' as [[ERC HP]|NEW]; [|exact NEW]. rewrite ERC.
      eapply rw_cells_agree; [exact AG| exact HRc|]. intros x Hx. apply HP. cbn in Hx. unfold RECP_SC_SZ. lia.
Qed.

(* [comment removed for export] *)
Theorem lib_state_hc_agree : forall cxo hs s m m' OW PL EA,
  lib_state_hc cxo hs s m OW PL EA -> agree_on (own_fpc cxo hs s OW PL EA) m m' -> lib_state_hc cxo hs s m' OW PL EA.
Proof.
  intros cxo hs s m m' OW PL EA (HC & (HE1 & HE2) & HO & (S1 & S2 & S3 & HM)) AG.
  assert (HL : forall a, ApBnRepA.libw a -> own_fpc cxo hs s OW PL EA a) by (intros a Ha; left; apply libw_bn; exact Ha).
  assert (HLW : forall a, libw a -> own_fpc cxo hs s OW PL EA a) by (intros a Ha; left; exact Ha).
  split; [eapply ApBnRepA.crypto_statics_agree; eauto|].
  split. { split; [eapply ApBnRepA.err_statics_agree; eauto|]. eapply ApBnRepA.err_mem_agree; [exact AG| exact HL| | | exact HE2]; [|auto].
           intros x Hx. do 4 right. exact Hx. }
  split; [exact (lib_cells_agree _ _ _ AG HL HLW HO)|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply gen_transport; [exact HM| exact AG| | auto| auto| auto| auto| auto| |].
  - intros Ec x Hx. right; right; left. split; [exact Ec| exact Hx].
  - intros x Hx. right; right; right; left. exact Hx.
  - intros r a HA [Hh|HRp]; [left; exact Hh|]. destruct (in_dec Nat.eq_dec r hs) as [Hi|Hn]; [left; exact Hi|]. right.
    eapply bn_rep_transport; [exact AG| | | exact HRp]; [|auto].
    intros x Hx. right; left. exists r, a. split; [exact HA|]. split; [eapply gen_ref_valid; eauto| auto].
Qed.

Definition lib_state_h_agree := lib_state_hc_agree false.

(* [comment removed for export] *)
Definition own_fpA (cxo : bool) (hs : list bnref) (s : ST) (OW : list block) (PL : placement) (EA : ApBnRepA.err_addrs) (x : Z) : Prop :=
  ApBnRepA.libw x
  \/ (exists r a, ref_at s OW PL r a /\ vref r s /\ ~ In r hs /\ r <> ROne /\ bn_fp OW (pl_of PL r) a (getbn r s) x)
  \/ (cxo = false /\ cx_fp s OW PL x)
  \/ mont_fp PL x
  \/ ApBnRepA.err_fp OW EA x.

Lemma own_fpA_fpc : forall cxo hs s OW PL EA x, own_fpA cxo hs s OW PL EA x -> own_fpc cxo hs s OW PL EA x.
Proof.
  intros cxo hs s OW PL EA x [HL|[(r & a & HA & HV & Hn & _ & HF)|[HC|[HM|HE]]]].
  - left. apply libw_bn. exact HL.
  - right; left. exists r, a. auto.
  - right; right; left. exact HC.
  - right; right; right; left. exact HM.
  - right; right; right; right. exact HE.
Qed.

Theorem lib_state_hc_agreeA : forall cxo hs s m m' OW PL EA,
  lib_state_hc cxo hs s m OW PL EA -> agree_on (own_fpA cxo hs s OW PL EA) m m' -> lib_state_hc cxo hs s m' OW PL EA.
Proof.
  intros cxo hs s m m' OW PL EA (HC & (HE1 & HE2) & (HO & _) & (S1 & S2 & S3 & HM)) AG.
  assert (HL : forall a, ApBnRepA.libw a -> own_fpA cxo hs s OW PL EA a) by (intros a Ha; left; exact Ha).
  split; [eapply ApBnRepA.crypto_statics_agree; eauto|].
  split. { split; [eapply ApBnRepA.err_statics_agree; eauto|]. eapply ApBnRepA.err_mem_agree; [exact AG| exact HL| | | exact HE2]; [|auto].
           intros x Hx. do 4 right. exact Hx. }
  split; [split; [eapply ApBnRepA.ossl_exit_cells_agree; eauto| exact I]|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply gen_transport; [exact HM| exact AG| | auto| auto| auto| auto| auto| |].
  - intros Ec x Hx. right; right; left. split; [exact Ec| exact Hx].
  - intros x Hx. right; right; right; left. exact Hx.
  - intros r a HA [Hh|HRp]; [left; exact Hh|]. destruct (in_dec Nat.eq_dec r hs) as [Hi|Hn]; [left; exact Hi|]. right.
    destruct (Nat.eq_dec r ROne) as [->|NRO].
    { (* [comment removed for export] *)
      rewrite pl_of_one in *. pose proof (proj1 (proj2 (proj2 S1))) as EONE. rewrite EONE in *.
      destruct HRp as (D & HCs & HAr). exists D. split; [exact HCs|]. unfold bn_arr in HAr |- *. cbn [bn_d bn_const_one] in HAr |- *. exact HAr. }
    eapply bn_rep_transport; [exact AG| | | exact HRp]; [|auto].
    intros x Hx. right; left. exists r, a. split; [exact HA|]. split; [eapply gen_ref_valid; eauto|]. split; [exact Hn|]. split; [exact NRO| exact Hx].
Qed.

(* [comment removed for export] *)
Lemma libw_clientA : forall L SP x, ApBnRepA.libw x -> aclient_addr L SP x.
Proof. intros L SP x H. right; left. apply LIBW_cs. exact H. Qed.

End WithCeiling1.
Notation own_fp := (own_fpc false).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section Ids.

Lemma In_concat_map_nth : forall (l : list BN) i p, (i < length l)%nat -> bn_d (nth i l (bn_nil 0)) = Some p ->
  In (p, 8 * Z.of_nat (bn_dmax (nth i l (bn_nil 0)))) (concat (map bn_blocks l)).
Proof.
  induction l as [|x l IH]; intros i p Hi Hd; cbn in Hi; [lia|]. cbn [map concat]. apply in_or_app. destruct i as [|i].
  - left. cbn [nth] in *. unfold bn_blocks. rewrite Hd. left. reflexivity.
  - right. cbn [nth] in *. apply IH; [lia| exact Hd].
Qed.

Lemma blocks_of_In_bn : forall r (s : ST) p, vref r s -> bn_d (getbn r s) = Some p -> In (p, 8 * Z.of_nat (bn_dmax (getbn r s))) (blocks_of s).
Proof. intros r s p Hv Hd. unfold blocks_of. apply in_or_app. left. apply In_concat_map_nth; assumption. Qed.

Lemma blocks_of_In_item : forall (s : ST) q, In q (gx_items (st_ctx s)) -> In (q, POOL_ITEM_BYTES) (blocks_of s).
Proof. intros s q H. unfold blocks_of. apply in_or_app; right. apply in_or_app; left. apply in_map_iff. exists q. auto. Qed.

Lemma blocks_of_In_idx : forall (s : ST) q, gx_indexes (st_ctx s) = Some q -> In (q, 4 * Z.of_nat BN_CTX_START_FRAMES) (blocks_of s).
Proof. intros s q H. unfold blocks_of. apply in_or_app; right. apply in_or_app; right. rewrite H. left. reflexivity. Qed.

Lemma bn_in_m : forall r (s : ST) p, vref r s -> bn_d (getbn r s) = Some p -> In p (map fst (blocks_of s)).
Proof. intros r s p Hv H. apply (blocks_of_In_bn r s p Hv) in H. apply (in_map fst) in H. exact H. Qed.
Lemma item_in_m : forall (s : ST) q, In q (gx_items (st_ctx s)) -> In q (map fst (blocks_of s)).
Proof. intros s q H. apply blocks_of_In_item in H. apply (in_map fst) in H. exact H. Qed.
Lemma idx_in_m : forall (s : ST) q, gx_indexes (st_ctx s) = Some q -> In q (map fst (blocks_of s)).
Proof. intros s q H. apply blocks_of_In_idx in H. apply (in_map fst) in H. exact H. Qed.

(* [comment removed for export] *)
Lemma ids_without : forall r (s : ST) p, List.NoDup (map fst (blocks_of s)) -> vref r s -> bn_d (getbn r s) = Some p ->
  ~ In p (map fst (blocks_of (setbn r (bn_nil 0) s))).
Proof.
  intros r s p ND Hv Hd. destruct (blocks_setbn r s Hv) as (R & H1 & H2).
  specialize (H2 (bn_nil 0)). cbn [bn_blocks bn_nil bn_d app] in H2.
  unfold bn_blocks in H1. rewrite Hd in H1. cbn [app] in H1.
  apply (Permutation_map fst) in H1. apply (Permutation_map fst) in H2. cbn [map fst] in H1.
  apply (Permutation_NoDup H1) in ND. apply NoDup_cons_iff in ND. destruct ND as [Hn _].
  intros Hin. apply Hn. eapply Permutation_in; [exact H2| exact Hin].
Qed.

Lemma ids_bn_neq : forall r r' (s : ST) p p', List.NoDup (map fst (blocks_of s)) -> vref r s -> vref r' s -> r <> r' ->
  bn_d (getbn r s) = Some p -> bn_d (getbn r' s) = Some p' -> p <> p'.
Proof.
  intros r r' s p p' ND Hv Hv' Hne Hd Hd' E. subst p'. apply (ids_without r s p ND Hv Hd).
  pose proof (blocks_of_In_bn r' (setbn r (bn_nil 0) s) p) as H. rewrite getbn_setbn_other in H by exact Hne.
  unfold vref in H. rewrite length_setbn in H. specialize (H Hv' Hd'). apply (in_map fst) in H. exact H.
Qed.

Lemma ids_bn_item_neq : forall r (s : ST) p q, List.NoDup (map fst (blocks_of s)) -> vref r s ->
  bn_d (getbn r s) = Some p -> In q (gx_items (st_ctx s)) -> p <> q.
Proof.
  intros r s p q ND Hv Hd Hq E. subst q. apply (ids_without r s p ND Hv Hd).
  apply item_in_m. rewrite st_ctx_setbn. exact Hq.
Qed.

Lemma ids_bn_idx_neq : forall r (s : ST) p q, List.NoDup (map fst (blocks_of s)) -> vref r s ->
  bn_d (getbn r s) = Some p -> gx_indexes (st_ctx s) = Some q -> p <> q.
Proof.
  intros r s p q ND Hv Hd Hq E. subst q. apply (ids_without r s p ND Hv Hd).
  apply idx_in_m. rewrite st_ctx_setbn. exact Hq.
Qed.

Lemma ids_item_idx_neq : forall (s : ST) h q, List.NoDup (map fst (blocks_of s)) ->
  In h (gx_items (st_ctx s)) -> gx_indexes (st_ctx s) = Some q -> h <> q.
Proof.
  intros s h q ND Hh Hq E. subst q. unfold blocks_of in ND. rewrite Hq in ND. cbn [opt_block] in ND.
  rewrite !map_app in ND. apply nodup_app_r in ND. rewrite map_map in ND. cbn [fst] in ND. rewrite map_id in ND.
  eapply (nodup_app_disj _ _ h ND Hh). left. reflexivity.
Qed.

Lemma ids_items_nodup : forall (s : ST), List.NoDup (map fst (blocks_of s)) -> List.NoDup (gx_items (st_ctx s)).
Proof.
  intros s ND. unfold blocks_of in ND. rewrite !map_app in ND. apply nodup_app_r in ND. apply nodup_app_l in ND.
  rewrite map_map in ND. cbn [fst] in ND. rewrite map_id in ND. exact ND.
Qed.

Lemma nth_error_nodup_inj : forall {A} (l : list A) k k' x, List.NoDup l -> nth_error l k = Some x -> nth_error l k' = Some x -> k = k'.
Proof.
  intros A l. induction l as [|y l IH]; intros k k' x ND Hk Hk'; [destruct k; discriminate Hk|].
  apply NoDup_cons_iff in ND. destruct ND as [Hy ND].
  destruct k as [|k]; destruct k' as [|k']; cbn [nth_error] in Hk, Hk'.
  - reflexivity.
  - exfalso. injection Hk as ->. apply Hy. eapply nth_error_In. exact Hk'.
  - exfalso. injection Hk' as ->. apply Hy. eapply nth_error_In. exact Hk.
  - f_equal. eapply IH; eauto.
Qed.

End Ids.

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeiling2. Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation SP0 := (@ar_SP0 AR).
Local Notation LIBW_cs := (@ar_LIBW_cs AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

(* [comment removed for export] *)
Lemma ids_pl_ea : forall s PL EA q q', ids_ok s PL EA -> In q (pl_ids PL) -> In q' (ApBnRepA.ea_ids EA) -> q <> q'.
Proof. intros s PL EA q q' ND H1 H2 E. subst q'. unfold ids_ok, all_ids in ND. eapply (nodup_app_disj _ _ q ND H1). apply in_or_app. left. exact H2. Qed.
Lemma ids_pl_m : forall s PL EA q q', ids_ok s PL EA -> In q (pl_ids PL) -> In q' (map fst (blocks_of s)) -> q <> q'.
Proof. intros s PL EA q q' ND H1 H2 E. subst q'. unfold ids_ok, all_ids in ND. eapply (nodup_app_disj _ _ q ND H1). apply in_or_app. right. exact H2. Qed.
Lemma ids_ea_m : forall s PL EA q q', ids_ok s PL EA -> In q (ApBnRepA.ea_ids EA) -> In q' (map fst (blocks_of s)) -> q <> q'.
Proof. intros s PL EA q q' ND H1 H2 E. subst q'. unfold ids_ok, all_ids in ND. apply nodup_app_r in ND. eapply (nodup_app_disj _ _ q ND H1). exact H2. Qed.
Lemma ids_m_nodup : forall s PL EA, ids_ok s PL EA -> List.NoDup (map fst (blocks_of s)).
Proof. intros s PL EA ND. unfold ids_ok, all_ids in ND. apply nodup_app_r in ND. apply nodup_app_r in ND. exact ND. Qed.
Lemma ids_pl_nodup : forall s PL EA, ids_ok s PL EA -> List.NoDup (pl_ids PL).
Proof. intros s PL EA ND. unfold ids_ok, all_ids in ND. apply nodup_app_l in ND. exact ND. Qed.

Lemma in_pl_ids_bn : forall PL r a q off, (r < NFIX)%nat -> pl_bn PL r = Some (PHeap a q off) -> In q (pl_ids PL).
Proof. intros PL r a q off Hr E. unfold pl_ids. apply in_or_app. left. apply pl_bn_ids_In. exists r, a, off. auto. Qed.
Lemma in_pl_ids_ctx : forall PL ac qc, pl_ctx PL = Some (ac, qc) -> In qc (pl_ids PL).
Proof. intros PL ac qc E. unfold pl_ids. rewrite E. apply in_or_app; right. apply in_or_app; left. left. reflexivity. Qed.
Lemma in_pl_ids_mont : forall PL am qm, pl_mont PL = Some (am, qm) -> In qm (pl_ids PL).
Proof. intros PL am qm E. unfold pl_ids. rewrite E. apply in_or_app; right. apply in_or_app; right. left. reflexivity. Qed.

Lemma ids_bn_ctx_neq : forall s PL EA r a q off ac qc, ids_ok s PL EA -> (r < NFIX)%nat ->
  pl_bn PL r = Some (PHeap a q off) -> pl_ctx PL = Some (ac, qc) -> q <> qc.
Proof.
  intros s PL EA r a q off ac qc ND Hr E Ec. apply ids_pl_nodup in ND. unfold pl_ids in ND. rewrite Ec in ND.
  intros ->. eapply (nodup_app_disj _ _ qc ND); [apply pl_bn_ids_In; exists r, a, off; auto| apply in_or_app; left; left; reflexivity].
Qed.
Lemma ids_bn_mont_neq : forall s PL EA r a q off am qm, ids_ok s PL EA -> (r < NFIX)%nat ->
  pl_bn PL r = Some (PHeap a q off) -> pl_mont PL = Some (am, qm) -> q <> qm.
Proof.
  intros s PL EA r a q off am qm ND Hr E Em. apply ids_pl_nodup in ND. unfold pl_ids in ND. rewrite Em in ND.
  intros ->. eapply (nodup_app_disj _ _ qm ND); [apply pl_bn_ids_In; exists r, a, off; auto| apply in_or_app; right; left; reflexivity].
Qed.
Lemma ids_ctx_mont_neq : forall s PL EA ac qc am qm, ids_ok s PL EA -> pl_ctx PL = Some (ac, qc) -> pl_mont PL = Some (am, qm) -> qc <> qm.
Proof.
  intros s PL EA ac qc am qm ND Ec Em. apply ids_pl_nodup in ND. unfold pl_ids in ND. rewrite Ec, Em in ND.
  apply nodup_app_r in ND. cbn [opt_ids app] in ND. apply NoDup_cons_iff in ND. destruct ND as [Hn _]. intros ->. apply Hn. left. reflexivity.
Qed.

(* [comment removed for export] *)
Inductive skind (s : ST) (OW : list block) (PL : placement) (r : bnref) (a : Z) : Prop :=
  | SK_own (q : bptr) (n : Z) : stored_ref r -> pl_bn PL r = Some (PHeap a q 0) -> In (q, a, n) OW -> BN_STRUCT_SZ <= n -> skind s OW PL r a
  | SK_mont (am : Z) (qm : bptr) : mont_ref r = true -> pl_mont PL = Some (am, qm) -> In (qm, am, MONT_CTX_SZ) OW ->
      a = am + 24 * Z.of_nat (r - RMontRR) -> 0 <= 24 * Z.of_nat (r - RMontRR) <= 48 -> skind s OW PL r a
  | SK_pool (i : nat) (q : bptr) (H : Z) : r = RPool i -> nth_error (gx_items (st_ctx s)) (i / BN_CTX_POOL_SIZE)%nat = Some q -> In (q, H, ITEM_SZ) OW ->
      a = H + 24 * Z.of_nat (i mod BN_CTX_POOL_SIZE)%nat -> (i mod BN_CTX_POOL_SIZE < BN_CTX_POOL_SIZE)%nat -> skind s OW PL r a
  | SK_frame (p : place) : stored_ref r -> pl_bn PL r = Some p -> In (a, a + BN_STRUCT_SZ) (fr_ivs (Some p)) -> In (a, a + BN_STRUCT_SZ) (pl_frames PL) ->
      skind s OW PL r a
  | SK_one : r = ROne -> a = CONST_ONE -> skind s OW PL r a.

Lemma ref_at_inb : forall s OW PL r a, pl_wf PL -> pl_blocks OW PL -> ref_at s OW PL r a -> skind s OW PL r a.
Proof.
  intros s OW PL r a WF (PB & _ & PM) HA. unfold ref_at in HA. destruct (Nat.ltb_spec r NFIX) as [Hr|Hr].
  - destruct HA as (p & E & Ea). destruct (pl_of_cases PL r p E) as [[-> ->]|[(am & qm & M & Em & -> & Hoff)|[S Eb]]].
    + apply SK_one; [reflexivity|]. cbn in Ea. congruence.
    + rewrite Em in PM. eapply (SK_mont s OW PL r a am qm M Em PM); [cbn in Ea; lia| exact Hoff].
    + pose proof (proj1 WF r p Eb) as (_ & _ & _ & Wp). pose proof (PB r p Hr E) as OK.
      destruct p as [x q off|x|x d|x]; cbn [place_addr] in Ea; subst x.
      * subst off. destruct OK as (n & Hin & _ & Hn). rewrite Z.sub_0_r in Hin. eapply (SK_own s OW PL r a q n S Eb Hin Hn).
      * eapply (SK_frame s OW PL r a (PFrame a) S Eb); [left; reflexivity|]. apply pl_frames_In. left. exists r. rewrite Eb. split; [exact Hr| left; reflexivity].
      * eapply (SK_frame s OW PL r a (PFrameBuf a d) S Eb); [left; reflexivity|]. apply pl_frames_In. left. exists r. rewrite Eb. split; [exact Hr| left; reflexivity].
      * destruct Wp.
  - destruct HA as (q & H & Eq & Hin & Ea). eapply (SK_pool s OW PL r a (r - NFIX)%nat q H); [unfold RPool; lia| exact Eq| exact Hin| exact Ea|].
    apply Nat.mod_upper_bound. unfold BN_CTX_POOL_SIZE. lia.
Qed.

(* [comment removed for export] *)
Definition frames_ok (PL : placement) (SPX BX : Z) : Prop := pl_frames_in PL SPX BX /\ ACEIL <= SPX /\ BX < 2^63.

Lemma frames_ok_mono : forall PL SPX SPX' BX, frames_ok PL SPX BX -> ACEIL <= SPX' <= SPX -> frames_ok PL SPX' BX.
Proof. intros PL SPX SPX' BX (H1 & H2 & H3) H. split; [eapply pl_frames_in_mono; [exact H1| lia| lia]| lia]. Qed.

Lemma frames_ok_empty : forall SPX BX, ACEIL <= SPX -> BX < 2^63 -> frames_ok pl_empty SPX BX.
Proof. intros. split; [apply pl_frames_in_empty| lia]. Qed.

Lemma frames_ok_set_ctx : forall PL c SPX BX, frames_ok PL SPX BX -> frames_ok (pl_set_ctx PL c) SPX BX.
Proof. intros PL c SPX BX H. exact H. Qed.
Lemma frames_ok_set_mont : forall PL mo SPX BX, frames_ok PL SPX BX -> frames_ok (pl_set_mont PL mo) SPX BX.
Proof. intros PL mo SPX BX H. exact H. Qed.
Lemma frames_ok_set_heap : forall PL r a q off SPX BX, frames_ok PL SPX BX -> fr_ivs (pl_bn PL r) = [] -> frames_ok (pl_set PL r (Some (PHeap a q off))) SPX BX.
Proof. intros PL r a q off SPX BX (H1 & H2) E. split; [apply pl_frames_in_set_heap; assumption| exact H2]. Qed.
Lemma frames_ok_set_none : forall PL r SPX BX, frames_ok PL SPX BX -> frames_ok (pl_set PL r None) SPX BX.
Proof. intros PL r SPX BX (H1 & H2). split; [apply pl_frames_in_set_none; assumption| exact H2]. Qed.

(* [comment removed for export] *)
Definition err_blocks (OW : list block) (EA : ApBnRepA.err_addrs) : Prop :=
  forall b, In b (ApBnRepA.ea_blks EA ++ ApBnRepA.ea_rsv EA) -> In b OW.   (* [comment removed for export] *)
Definition lib_parts (st : ST) (OW : list block) (PL : placement) (EA : ApBnRepA.err_addrs) : Prop :=
  st_wf st /\ pl_wf PL /\ ids_ok st PL EA /\ pl_blocks OW PL /\ err_blocks OW EA.

Section Disj.
  Variables (s : rts RT) (OW LB : list block) (m : mem).
  Hypothesis HEAP : AHEAP s OW LB m.

  Lemma blk_excl : forall q1 A1 n1 q2 A2 n2 x,
    In (q1, A1, n1) OW -> In (q2, A2, n2) OW -> q1 <> q2 -> A1 <= x < A1 + n1 -> A2 <= x < A2 + n2 -> False.
  Proof. intros q1 A1 n1 q2 A2 n2 x H1 H2 NE R1 R2. pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP H1 H2 NE). lia. Qed.

  Lemma blk_not_libw : forall q A n x, In (q, A, n) OW -> A <= x < A + n -> libw x -> False.
  Proof.
    intros q A n x Hin Hx HL. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & _ & BI).
    revert HL. unfold libw, LIBW_bgr, ARun.LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia.
  Qed.

  Lemma blk_below_ceiling : forall q A n x, In (q, A, n) OW -> A <= x < A + n -> x < ACEIL.
  Proof. intros q A n x Hin Hx. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & BC & _). lia. Qed.

  Lemma blk_not_image : forall q A n x, In (q, A, n) OW -> A <= x < A + n -> 0x10000 <= x < 0xbcb000 -> False.
  Proof. intros q A n x Hin Hx HI. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & _ & BI). lia. Qed.

  Variables (st : ST) (PL : placement) (EA : ApBnRepA.err_addrs) (SPX BX : Z).
  Hypothesis PARTS : lib_parts st OW PL EA.
  Hypothesis FROK : frames_ok PL SPX BX.
  Local Ltac parts := pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).

  Local Ltac std_lia__ := lia.
  Local Ltac clia := pose proof (AH_ceil _ _ _ _ HEAP) as CEIL_RANGE__; unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CEIL_RANGE__; std_lia__.

  Lemma frame_iv_range : forall iv, In iv (pl_frames PL) -> ACEIL <= fst iv /\ SPX <= fst iv /\ snd iv < 2^63.
  Proof. parts. intros iv H. destruct FROK as (PLF & CSP & BXB). destruct (PLF iv H). lia. Qed.

  Lemma const_one_image : 0x10000 <= CONST_ONE /\ CONST_ONE + BN_STRUCT_SZ <= 0xbcb000 /\ 0x10000 <= DATA_ONE /\ DATA_ONE + 8 <= 0xbcb000.
  Proof. parts. unfold CONST_ONE, DATA_ONE, BN_STRUCT_SZ. lia. Qed.

  (* [comment removed for export] *)
  Lemma skind_cases : forall r a, skind st OW PL r a ->
       (exists q A n, In (q, A, n) OW /\ A <= a /\ a + BN_STRUCT_SZ <= A + n /\ (In q (pl_ids PL) \/ In q (gx_items (st_ctx st))))
    \/ (In (a, a + BN_STRUCT_SZ) (pl_frames PL) /\ ACEIL <= a /\ a + BN_STRUCT_SZ < 2^63)
    \/ (r = ROne /\ a = CONST_ONE).
  Proof.
    parts.
    intros r a K. destruct K as [q n S Eb Hin Hn|am qm M Em Hin -> Hoff|i q H -> Eq Hin -> Hj|p S Eb Hiv HF| -> ->].
    - left. exists q, a, n. split; [exact Hin|]. split; [lia|]. split; [lia|]. left. eapply in_pl_ids_bn; [exact (proj1 S)| exact Eb].
    - left. exists qm, am, MONT_CTX_SZ. split; [exact Hin|]. unfold BN_STRUCT_SZ, MONT_CTX_SZ in *. split; [lia|]. split; [lia|]. left. eapply in_pl_ids_mont. exact Em.
    - left. exists q, H, ITEM_SZ. split; [exact Hin|]. unfold ITEM_SZ, POOL_ITEM_BYTES, BN_STRUCT_SZ, BN_CTX_POOL_SIZE in *. split; [lia|]. split; [nia|].
      right. eapply nth_error_In. exact Eq.
    - right; left. split; [exact HF|]. destruct (frame_iv_range _ HF) as (H1 & _ & H2). cbn [fst snd] in H1, H2. lia.
    - right; right. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma sk_block_own : forall r a q n, pl_bn PL r = Some (PHeap a q 0) -> In (q, a, n) OW -> BN_STRUCT_SZ <= n ->
    a + 24 <= ACEIL /\ (a + 24 <= 0x10000 \/ 0xbcb000 <= a) /\ 0 < a.
  Proof. parts. intros r a q n _ Hin Hn. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI). unfold BN_STRUCT_SZ in *. lia. Qed.
  Lemma sk_block_mont : forall am qm a, In (qm, am, MONT_CTX_SZ) OW -> a = am + 24 * Z.of_nat 0 \/ True -> am <= a -> a + 24 <= am + MONT_CTX_SZ ->
    a + 24 <= ACEIL /\ (a + 24 <= 0x10000 \/ 0xbcb000 <= a) /\ 0 < a.
  Proof. parts. intros am qm a Hin _ H1 H2. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI). unfold MONT_CTX_SZ in *. lia. Qed.
  Lemma sk_block_pool : forall q H a j, In (q, H, ITEM_SZ) OW -> a = H + 24 * Z.of_nat j -> (j < BN_CTX_POOL_SIZE)%nat ->
    a + 24 <= ACEIL /\ (a + 24 <= 0x10000 \/ 0xbcb000 <= a) /\ 0 < a.
  Proof. parts. intros q H a j Hin -> Hj. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI). unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. lia. Qed.
  Lemma sk_frame : forall a, In (a, a + BN_STRUCT_SZ) (pl_frames PL) -> ACEIL <= a /\ a + 24 < 2^63.
  Proof. parts. intros a H. destruct (frame_iv_range _ H) as (H1 & _ & H2). cbn [fst snd] in H1, H2. unfold BN_STRUCT_SZ in *. lia. Qed.

  (* [comment removed for export] *)
  Lemma skind_range : forall r a, skind st OW PL r a ->
    (a + 24 <= ACEIL /\ (a + 24 <= 0x10000 \/ 0xbcb000 <= a) /\ 0 < a) \/ (ACEIL <= a /\ a + 24 < 2^63) \/ (r = ROne /\ a = CONST_ONE).
  Proof.
    parts.
    intros r a K. destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
    - left. eapply sk_block_own; eauto.
    - left. eapply (sk_block_mont am qm a Hin); [right; exact I| lia| unfold MONT_CTX_SZ in *; lia].
    - left. eapply sk_block_pool; eauto.
    - right; left. apply sk_frame. exact HF.
    - right; right. auto.
  Qed.

  (* [comment removed for export] *)
  Lemma struct_disj : forall r r' a a', r <> r' -> ref_at st OW PL r a -> ref_at st OW PL r' a' -> a + 24 <= a' \/ a' + 24 <= a.
  Proof.
    parts.
    intros r r' a a' NE HA HA'.
    pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K. pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA') as K'.
    pose proof (ids_m_nodup _ _ _ IDS) as NDm. pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (skind_range r a K) as RK. pose proof (skind_range r' a' K') as RK'. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
    (* [comment removed for export] *)
    destruct RK as [(C1 & I1 & P1)|[[C1 U1]|[-> ->]]]; destruct RK' as [(C2 & I2 & P2)|[[C2 U2]|[-> ->]]];
      try (unfold CONST_ONE in *; lia).
    - (* [comment removed for export] *)
      destruct K as [q1 n1 S1 Eb1 Hin1 Hn1|am qm M Em Hinm Ea Hoff|i qi H Er Eq Hini Ea Hj|p S1 Eb1 Hiv1 HF1|Er Ea1];
        [| | | exfalso; destruct (sk_frame a HF1); lia| exfalso; subst; unfold CONST_ONE in *; lia];
      destruct K' as [q2 n2 S2 Eb2 Hin2 Hn2|am' qm' M' Em' Hinm' Ea' Hoff'|i' qi' H' Er' Eq' Hini' Ea' Hj'|p' S2 Eb2 Hiv2 HF2|Er' Ea2];
        try (exfalso; destruct (sk_frame a' HF2); lia); try (exfalso; subst; unfold CONST_ONE in *; lia); unfold BN_STRUCT_SZ, MONT_CTX_SZ in *.
      + (* [comment removed for export] *)
        destruct (decide (q1 = q2)) as [E12|N12].
        * exfalso. subst q2. eapply (pl_bn_ids_nodup_neq PL NFIX r r' a a' q1 q1 0 0); try eassumption; try reflexivity.
          -- apply ids_pl_nodup in IDS. unfold pl_ids in IDS. apply nodup_app_l in IDS. exact IDS.
          -- exact (proj1 S1).
          -- exact (proj1 S2).
        * pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hin1 Hin2 N12). lia.
      + (* [comment removed for export] *) destruct (decide (q1 = qm')) as [->|N]; [exfalso; eapply (ids_bn_mont_neq st PL EA r a qm' 0 am' qm'); eauto; exact (proj1 S1)|].
        pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hin1 Hinm' N). lia.
      + (* [comment removed for export] *) destruct (decide (q1 = qi')) as [->|N].
        * exfalso. eapply (ids_pl_m st PL EA qi' qi' IDS); [eapply in_pl_ids_bn; [exact (proj1 S1)| exact Eb1]| apply item_in_m; eapply nth_error_In; exact Eq'| reflexivity].
        * pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hin1 Hini' N). unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. lia.
      + (* [comment removed for export] *) destruct (decide (q2 = qm)) as [->|N]; [exfalso; eapply (ids_bn_mont_neq st PL EA r' a' qm 0 am qm); eauto; exact (proj1 S2)|].
        pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hin2 Hinm N). lia.
      + (* [comment removed for export] *)
        rewrite Em in Em'. injection Em' as <- <-. apply mont_ref_cases in M. apply mont_ref_cases in M'.
        destruct M as [->|[->| ->]]; destruct M' as [->|[->| ->]]; try (exfalso; apply NE; reflexivity); cbn in Ea, Ea'; lia.
      + (* [comment removed for export] *) destruct (decide (qm = qi')) as [->|N].
        * exfalso. eapply (ids_pl_m st PL EA qi' qi' IDS); [eapply in_pl_ids_mont; exact Em| apply item_in_m; eapply nth_error_In; exact Eq'| reflexivity].
        * pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hinm Hini' N). unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. lia.
      + (* [comment removed for export] *) destruct (decide (q2 = qi)) as [->|N].
        * exfalso. eapply (ids_pl_m st PL EA qi qi IDS); [eapply in_pl_ids_bn; [exact (proj1 S2)| exact Eb2]| apply item_in_m; eapply nth_error_In; exact Eq| reflexivity].
        * pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hin2 Hini N). unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. lia.
      + (* [comment removed for export] *) destruct (decide (qm' = qi)) as [->|N].
        * exfalso. eapply (ids_pl_m st PL EA qi qi IDS); [eapply in_pl_ids_mont; exact Em'| apply item_in_m; eapply nth_error_In; exact Eq| reflexivity].
        * pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hinm' Hini N). unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. lia.
      + (* [comment removed for export] *)
        destruct (decide (qi = qi')) as [E|N].
        2:{ pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hini Hini' N). unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. nia. }
        subst qi'. destruct (AH_addr_unique OW qi H ITEM_SZ H' ITEM_SZ ND Hini Hini') as [<- _].
        assert (Ek : (i / BN_CTX_POOL_SIZE)%nat = (i' / BN_CTX_POOL_SIZE)%nat).
        { eapply nth_error_nodup_inj; [apply ids_items_nodup; exact NDm| exact Eq| exact Eq']. }
        assert (i <> i') by (intros ->; apply NE; congruence).
        pose proof (Nat.div_mod_eq i BN_CTX_POOL_SIZE). pose proof (Nat.div_mod_eq i' BN_CTX_POOL_SIZE).
        assert ((i mod BN_CTX_POOL_SIZE)%nat <> (i' mod BN_CTX_POOL_SIZE)%nat) by (unfold BN_CTX_POOL_SIZE in *; lia).
        subst a a'. unfold BN_CTX_POOL_SIZE in *. nia.
    - (* [comment removed for export] *)
      destruct K as [q1 n1 S1 Eb1 Hin1 Hn1|am qm M Em Hinm Ea Hoff|i qi H Er Eq Hini Ea Hj|p S1 Eb1 Hiv1 HF1|Er Ea1];
        [exfalso; destruct (sk_block_own _ _ _ _ Eb1 Hin1 Hn1); lia
        | exfalso; destruct (sk_block_mont am qm a Hinm ltac:(right; exact I) ltac:(lia) ltac:(unfold MONT_CTX_SZ in *; lia)); lia
        | exfalso; destruct (sk_block_pool _ _ _ _ Hini Ea Hj); lia | | exfalso; subst; unfold CONST_ONE in *; lia].
      destruct K' as [q2 n2 S2 Eb2 Hin2 Hn2|am' qm' M' Em' Hinm' Ea' Hoff'|i' qi' H' Er' Eq' Hini' Ea' Hj'|p' S2 Eb2 Hiv2 HF2|Er' Ea2];
        [exfalso; destruct (sk_block_own _ _ _ _ Eb2 Hin2 Hn2); lia
        | exfalso; destruct (sk_block_mont am' qm' a' Hinm' ltac:(right; exact I) ltac:(lia) ltac:(unfold MONT_CTX_SZ in *; lia)); lia
        | exfalso; destruct (sk_block_pool _ _ _ _ Hini' Ea' Hj'); lia | | exfalso; subst; unfold CONST_ONE in *; lia].
      pose proof (proj1 (proj2 PWF) r r' p p' _ _ NE Eb1 Eb2 Hiv1 Hiv2) as AP. unfold iv_apart, BN_STRUCT_SZ in AP. cbn [fst snd] in AP. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma struct_limbs_disj : forall r r' a p D n, ref_at st OW PL r a -> vref r' st -> bn_d (getbn r' st) = Some p ->
    In (p, D, n) OW -> a + 24 <= D \/ D + n <= a.
  Proof.
    parts.
    intros r r' a p D n HA HV' Ed Hin. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
    pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K. pose proof (ids_m_nodup _ _ _ IDS) as NDm.
    pose proof (bn_in_m r' st p HV' Ed) as Hm. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & Bn & BC & BI).
    destruct (skind_cases r a K) as [(q & A & nq & HinA & R1 & R2 & Hq)|[(HF & FA & FB)|[-> ->]]]; unfold BN_STRUCT_SZ in *.
    - assert (NE : q <> p).
      { destruct Hq as [Hq|Hq]; [eapply ids_pl_m; eauto|]. intros ->. eapply (ids_bn_item_neq r' st p p); eauto. }
      pose proof (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP HinA Hin NE). lia.
    - right. lia.
    - unfold CONST_ONE. lia.
  Qed.

  Lemma limbs_limbs_disj : forall r r' p D n p' D' n', r <> r' -> vref r st -> vref r' st ->
    bn_d (getbn r st) = Some p -> bn_d (getbn r' st) = Some p' -> In (p, D, n) OW -> In (p', D', n') OW ->
    D + n <= D' \/ D' + n' <= D.
  Proof.
    parts.
    intros r r' p D n p' D' n' NE HV HV' Ed Ed' Hin Hin'.
    assert (NEp : p <> p') by (eapply (ids_bn_neq r r' st p p'); eauto using ids_m_nodup).
    exact (AH_disjoint _ _ _ _ _ _ _ _ _ _ HEAP Hin Hin' NEp).
  Qed.

  (* [comment removed for export] *)
  Lemma framebuf_struct_disj : forall r ab d r' a', pl_bn PL r = Some (PFrameBuf ab d) -> ref_at st OW PL r' a' ->
    a' + 24 <= d \/ d + TMOD_BUF_SZ <= a'.
  Proof.
    parts.
    intros r ab d r' a' Eb HA'. pose proof (pl_wf_stored PL r _ PWF Eb) as S. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
    assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
    { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
    destruct (frame_iv_range _ HFd) as (Cd & _ & Ud). cbn [fst snd] in Cd, Ud.
    pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA') as K'.
    destruct (skind_range r' a' K') as [(C2 & I2 & P2)|[[C2 U2]|[-> ->]]]; [left; lia| | left; unfold CONST_ONE; pose proof (AH_ceil _ _ _ _ HEAP) as CR__; unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR__; lia].
    destruct K' as [q2 n2 S2 Eb2 Hin2 Hn2|am' qm' M' Em' Hinm' Ea' Hoff'|i' qi' H' Er' Eq' Hini' Ea' Hj'|p' S2 Eb2 Hiv2 HF2|Er' Ea2];
      [exfalso; destruct (sk_block_own _ _ _ _ Eb2 Hin2 Hn2); lia
      | exfalso; destruct (sk_block_mont am' qm' a' Hinm' ltac:(right; exact I) ltac:(lia) ltac:(unfold MONT_CTX_SZ in *; lia)); lia
      | exfalso; destruct (sk_block_pool _ _ _ _ Hini' Ea' Hj'); lia | | exfalso; subst; unfold CONST_ONE in *; lia].
    destruct (Nat.eq_dec r r') as [<-|NE].
    - rewrite Eb in Eb2. injection Eb2 as <-. cbn [fr_ivs In] in Hiv2. destruct Hiv2 as [E|[E|[]]].
      + injection E as <-. pose proof (proj1 PWF r _ Eb) as (_ & _ & _ & _ & _ & AP). unfold iv_apart, BN_STRUCT_SZ in AP. cbn [fst snd] in AP. lia.
      + injection E as E1 E2. unfold BN_STRUCT_SZ, TMOD_BUF_SZ in *. lia.
    - pose proof (proj1 (proj2 PWF) r r' _ _ (d, d + TMOD_BUF_SZ) (a', a' + BN_STRUCT_SZ) NE Eb Eb2 ltac:(right; left; reflexivity) Hiv2) as AP.
      unfold iv_apart, BN_STRUCT_SZ in AP. cbn [fst snd] in AP. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma bn_arr_facts : forall r D, vref r st -> r <> ROne -> bn_arr m OW (pl_of PL r) D (getbn r st) ->
    u64arr ctasegs m D (wlimbs (bn_buf (getbn r st)))
    /\ Z.of_nat (length (wlimbs (bn_buf (getbn r st)))) = Z.of_nat (bn_dmax (getbn r st))
    /\ 0 <= D /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= ACEIL \/ (SPX <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r st)) < 2^63))
    /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= 0x10000 \/ 0xbcb000 <= D \/ bn_dmax (getbn r st) = 0%nat)
    /\ (forall r' a', ref_at st OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= a').
  Proof.
    parts.
    intros r D HV HNO HArr. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR. unfold bn_arr in HArr. destruct (bn_d (getbn r st)) as [p|] eqn:Ed.
    - destruct HArr as [Hin HU]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI).
      split; [exact HU|]. split; [rewrite wlimbs_length; reflexivity|]. split; [lia|]. split; [left; exact BC|]. split; [lia|].
      intros r' a' HA'. eapply (struct_limbs_disj r' r); eauto.
    - assert (EMP : D = 0 /\ bn_buf (getbn r st) = [] ->
        u64arr ctasegs m D (wlimbs (bn_buf (getbn r st))) /\ Z.of_nat (length (wlimbs (bn_buf (getbn r st)))) = Z.of_nat (bn_dmax (getbn r st))
        /\ 0 <= D /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= ACEIL \/ (SPX <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r st)) < 2^63))
        /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= 0x10000 \/ 0xbcb000 <= D \/ bn_dmax (getbn r st) = 0%nat)
        /\ (forall r' a', ref_at st OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= a')).
      { intros [-> Eb]. unfold bn_dmax. rewrite Eb. cbn [length wlimbs map].
        split. { split; [apply bytes_at_nil; lia|]. cbn [length]. split; [lia|]. split; [lia|]. intros i Hi. lia. }
        split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [right; right; reflexivity|].
        intros r' a' HA'. right. pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA') as K'.
        destruct (skind_range r' a' K') as [(C2 & I2 & P2)|[[C2 U2]|[-> ->]]]; [lia| lia| unfold CONST_ONE; lia]. }
      destruct (pl_of PL r) as [[x q off|x|x d|x]|] eqn:Ep; try (apply EMP; exact HArr).
      + (* [comment removed for export] *)
        destruct HArr as (-> & HU & HL).
        destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [contradiction| discriminate E'|].
        assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
        { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
        destruct (frame_iv_range _ HFd) as (Cd & Sd & Ud). cbn [fst snd] in Cd, Sd, Ud.
        unfold bn_dmax. rewrite wlimbs_length, HL. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. unfold TMOD_BUF_SZ in *.
        split; [exact HU|]. split; [reflexivity|]. split; [lia|]. split; [right; lia|]. split; [right; left; lia|].
        intros r' a' HA'. pose proof (framebuf_struct_disj r x d r' a' Eb HA'). unfold TMOD_BUF_SZ in *. lia.
      + (* [comment removed for export] *)
        exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [contradiction| discriminate E'|].
        pose proof (proj1 PWF r _ Eb) as (_ & _ & _ & F). exact F.
  Qed.

  (* [comment removed for export] *)
  Inductive w_okc (cxo : bool) (hs : list bnref) (iv : Z * Z) : Prop :=
  | w_stack : ACEIL <= fst iv -> snd iv <= SPX -> w_okc cxo hs iv
  | w_struct : forall r a, In r hs -> ref_at st OW PL r a -> r <> ROne -> a <= fst iv -> snd iv <= a + 24 -> w_okc cxo hs iv
  | w_limbs : forall r p D, In r hs -> vref r st -> bn_d (getbn r st) = Some p ->
                In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) OW -> D <= fst iv -> snd iv <= D + 8 * Z.of_nat (bn_dmax (getbn r st)) ->
                w_okc cxo hs iv
  | w_foreign : forall q A n, In (q, A, n) (OW ++ LB) -> ~ In q (all_ids st PL EA) -> A <= fst iv -> snd iv <= A + n -> w_okc cxo hs iv
  | w_cx : cxo = true -> (forall x, fst iv <= x < snd iv -> cx_fp st OW PL x) -> w_okc cxo hs iv.

  (* [comment removed for export] *)
  Lemma cx_fp_block : forall x, cx_fp st OW PL x ->
    exists q A n, In (q, A, n) OW /\ A <= x < A + n /\ In q (all_ids st PL EA).
  Proof.
    parts.
    intros x [(ac & qc & Ec & Hx)|[(q & H & Hq & Hin & Hx)|(q & I & Eq & Hin & Hx)]]; unfold all_ids.
    - exists qc, ac, BN_CTX_SZ. destruct PLB as (_ & PC & _). rewrite Ec in PC. split; [exact PC|]. split; [exact Hx|].
      apply in_or_app; left. eapply in_pl_ids_ctx. exact Ec.
    - exists q, H, ITEM_SZ. split; [exact Hin|]. split; [unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia|].
      apply in_or_app; right; apply in_or_app; right. apply item_in_m. exact Hq.
    - exists q, I, FRAMES_SZ. split; [exact Hin|]. split; [exact Hx|]. apply in_or_app; right; apply in_or_app; right. apply idx_in_m. exact Eq.
  Qed.

  (* [comment removed for export] *)
  Lemma mont_fp_block : forall x, mont_fp PL x ->
    (exists q A n, In (q, A, n) OW /\ A <= x < A + n /\ In q (all_ids st PL EA)) \/ (exists iv, In iv (pl_frames PL) /\ fst iv <= x < snd iv).
  Proof.
    parts. intros x [(am & qm & Em & Hx)|(c & Ec & Hx)]; unfold all_ids.
    - left. exists qm, am, MONT_CTX_SZ. destruct PLB as (_ & _ & PM). rewrite Em in PM. split; [exact PM|]. split; [unfold MONT_CTX_SZ in *; lia|].
      apply in_or_app; left. eapply in_pl_ids_mont. exact Em.
    - right. exists (c, c + RECP_SC_SZ). split; [apply pl_frames_recp; exact Ec| cbn [fst snd]; exact Hx].
  Qed.

  (* [comment removed for export] *)
  Lemma own_fp_block : forall cxo hs x, own_fpc cxo hs st OW PL EA x ->
    libw x \/ (exists q A n, In (q, A, n) OW /\ A <= x < A + n /\ In q (all_ids st PL EA)) \/ (exists iv, In iv (pl_frames PL) /\ fst iv <= x < snd iv).
  Proof.
    parts.
    intros cxo hs x [HL|[(r & a & HA & HV & Hn & [Hs|[(p & D & Ed & Hin & Hx)|(y & d & Ep & Hx)]])|[[_ Hc]|[Hmo|He]]]]; unfold all_ids.
    - left. exact HL.
    - pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K.
      destruct K as [q n S Eb Hin Hn'|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
      + right; left. exists q, a, n. split; [exact Hin|]. unfold BN_STRUCT_SZ in *. split; [lia|]. apply in_or_app; left. eapply in_pl_ids_bn; [exact (proj1 S)| exact Eb].
      + right; left. exists qm, am, MONT_CTX_SZ. split; [exact Hin|]. unfold MONT_CTX_SZ in *. split; [lia|]. apply in_or_app; left. eapply in_pl_ids_mont; exact Em.
      + right; left. exists q, H, ITEM_SZ. split; [exact Hin|]. unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. split; [nia|].
        apply in_or_app; right; apply in_or_app; right. apply item_in_m. eapply nth_error_In. exact Eq.
      + right; right. exists (a, a + BN_STRUCT_SZ). split; [exact HF|]. cbn [fst snd]. unfold BN_STRUCT_SZ. lia.
      + left. subst. apply libw_const_one. unfold BN_STRUCT_SZ. lia.
    - right; left. exists p, D, (8 * Z.of_nat (bn_dmax (getbn r st))). split; [exact Hin|]. split; [exact Hx|].
      apply in_or_app; right; apply in_or_app; right. eapply bn_in_m; eauto.
    - right; right. destruct (pl_of_cases PL r _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [discriminate E'| discriminate E'|].
      exists (d, d + TMOD_BUF_SZ). split; [|cbn [fst snd]; exact Hx]. apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity].
    - right; left. apply cx_fp_block. exact Hc.
    - destruct (mont_fp_block x Hmo) as [HB|HFr]; [right; left; exact HB| right; right; exact HFr].
    - right; left. unfold ApBnRepA.err_fp, in_block in He. destruct He as ([[q A] n] & Hb & Hx). cbn [blk_addr blk_size fst snd] in Hx.
      exists q, A, n. split; [apply ERRB; apply in_or_app; left; exact Hb|]. split; [exact Hx|]. apply in_or_app; right; apply in_or_app; left.
      eapply ApBnRepA.ea_ids_blk. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma own_fp_blockA : forall cxo hs x, own_fpA cxo hs st OW PL EA x ->
    ApBnRepA.libw x \/ (exists q A n, In (q, A, n) OW /\ A <= x < A + n /\ In q (all_ids st PL EA)) \/ (exists iv, In iv (pl_frames PL) /\ fst iv <= x < snd iv).
  Proof.
    parts.
    intros cxo hs x [HL|[(r & a & HA & HV & Hn & HNO & [Hs|[(p & D & Ed & Hin & Hx)|(y & d & Ep & Hx)]])|[[_ Hc]|[Hmo|He]]]]; unfold all_ids.
    - left. exact HL.
    - pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K.
      destruct K as [q n S Eb Hin Hn'|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
      + right; left. exists q, a, n. split; [exact Hin|]. unfold BN_STRUCT_SZ in *. split; [lia|]. apply in_or_app; left. eapply in_pl_ids_bn; [exact (proj1 S)| exact Eb].
      + right; left. exists qm, am, MONT_CTX_SZ. split; [exact Hin|]. unfold MONT_CTX_SZ in *. split; [lia|]. apply in_or_app; left. eapply in_pl_ids_mont; exact Em.
      + right; left. exists q, H, ITEM_SZ. split; [exact Hin|]. unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. split; [nia|].
        apply in_or_app; right; apply in_or_app; right. apply item_in_m. eapply nth_error_In. exact Eq.
      + right; right. exists (a, a + BN_STRUCT_SZ). split; [exact HF|]. cbn [fst snd]. unfold BN_STRUCT_SZ. lia.
      + exfalso. exact (HNO Er).
    - right; left. exists p, D, (8 * Z.of_nat (bn_dmax (getbn r st))). split; [exact Hin|]. split; [exact Hx|].
      apply in_or_app; right; apply in_or_app; right. eapply bn_in_m; eauto.
    - right; right. destruct (pl_of_cases PL r _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [discriminate E'| discriminate E'|].
      exists (d, d + TMOD_BUF_SZ). split; [|cbn [fst snd]; exact Hx]. apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity].
    - right; left. apply cx_fp_block. exact Hc.
    - destruct (mont_fp_block x Hmo) as [HB|HFr]; [right; left; exact HB| right; right; exact HFr].
    - right; left. unfold ApBnRepA.err_fp, in_block in He. destruct He as ([[q A] n] & Hb & Hx). cbn [blk_addr blk_size fst snd] in Hx.
      exists q, A, n. split; [apply ERRB; apply in_or_app; left; exact Hb|]. split; [exact Hx|]. apply in_or_app; right; apply in_or_app; left.
      eapply ApBnRepA.ea_ids_blk. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma struct_not_cx : forall r a x, ref_at st OW PL r a -> a <= x < a + 24 -> cx_fp st OW PL x -> False.
  Proof.
    parts.
    intros r a x HA Hx HC. pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K. pose proof (ids_m_nodup _ _ _ IDS) as NDm. pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
    pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
    destruct (cx_fp_block x HC) as (qb & Ab & nb & Hinb & Hxb & _).
    destruct (skind_range r a K) as [(C1 & I1 & P1)|[[C1 U1]|[-> ->]]].
    2:{ pose proof (blk_below_ceiling qb Ab nb x Hinb Hxb). lia. }
    2:{ pose proof (AH_range _ _ _ _ _ _ _ HEAP Hinb) as (_ & _ & _ & _ & BI). unfold CONST_ONE in *. lia. }
    (* [comment removed for export] *)
    destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea];
      [| | | exfalso; destruct (sk_frame a HF); lia| exfalso; subst; unfold CONST_ONE in *; lia]; unfold BN_STRUCT_SZ, MONT_CTX_SZ in *.
    - assert (Hxa : a <= x < a + n) by lia.
      destruct HC as [(ac & qc & Ec & Hc)|[(q' & H' & Hq' & Hin' & Hc)|(q' & I & Eq' & Hin' & Hc)]].
      + destruct PLB as (_ & PC & _). rewrite Ec in PC. eapply (blk_excl q a n qc ac BN_CTX_SZ x Hin PC); [| exact Hxa| exact Hc].
        eapply ids_bn_ctx_neq; eauto. exact (proj1 S).
      + eapply (blk_excl q a n q' H' ITEM_SZ x Hin Hin'); [| exact Hxa| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia].
        eapply ids_pl_m; [exact IDS| eapply in_pl_ids_bn; [exact (proj1 S)| exact Eb]| apply item_in_m; exact Hq'].
      + eapply (blk_excl q a n q' I FRAMES_SZ x Hin Hin'); [| exact Hxa| exact Hc].
        eapply ids_pl_m; [exact IDS| eapply in_pl_ids_bn; [exact (proj1 S)| exact Eb]| apply idx_in_m; exact Eq'].
    - assert (Hxa : am <= x < am + 96) by lia.
      destruct HC as [(ac & qc & Ec & Hc)|[(q' & H' & Hq' & Hin' & Hc)|(q' & I & Eq' & Hin' & Hc)]].
      + destruct PLB as (_ & PC & _). rewrite Ec in PC. eapply (blk_excl qm am 96 qc ac BN_CTX_SZ x Hin PC); [| exact Hxa| exact Hc].
        intros E. eapply ids_ctx_mont_neq; eauto.
      + eapply (blk_excl qm am 96 q' H' ITEM_SZ x Hin Hin'); [| exact Hxa| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia].
        eapply ids_pl_m; [exact IDS| eapply in_pl_ids_mont; exact Em| apply item_in_m; exact Hq'].
      + eapply (blk_excl qm am 96 q' I FRAMES_SZ x Hin Hin'); [| exact Hxa| exact Hc].
        eapply ids_pl_m; [exact IDS| eapply in_pl_ids_mont; exact Em| apply idx_in_m; exact Eq'].
    - assert (Hxa : H <= x < H + 384) by (unfold BN_CTX_POOL_SIZE in *; nia).
      destruct HC as [(ac & qc & Ec & Hc)|[(q' & H' & Hq' & Hin' & Hc)|(q' & I & Eq' & Hin' & Hc)]].
      + destruct PLB as (_ & PC & _). rewrite Ec in PC. eapply (blk_excl q H ITEM_SZ qc ac BN_CTX_SZ x Hin PC); [| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia| exact Hc].
        intros ->. eapply (ids_pl_m st PL EA qc qc IDS); [eapply in_pl_ids_ctx; exact Ec| apply item_in_m; eapply nth_error_In; exact Eq| reflexivity].
      + destruct (decide (q = q')) as [->|NE].
        * destruct (AH_addr_unique OW q' H ITEM_SZ H' ITEM_SZ ND Hin Hin') as [<- _]. lia.
        * eapply (blk_excl q H ITEM_SZ q' H' ITEM_SZ x Hin Hin' NE); unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia.
      + eapply (blk_excl q H ITEM_SZ q' I FRAMES_SZ x Hin Hin'); [| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia| exact Hc].
        eapply ids_item_idx_neq; [exact NDm| eapply nth_error_In; exact Eq| exact Eq'].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma recp_frame : forall c, pl_recp PL = Some c -> ACEIL <= c /\ SPX <= c /\ c + RECP_SC_SZ < 2^63 /\ 0 < c.
  Proof.
    parts. intros c Ec. destruct (frame_iv_range _ (pl_frames_recp PL c Ec)) as (H1 & H2 & H3). cbn [fst snd] in H1, H2, H3.
    pose proof (proj2 (proj2 PWF)) as RC. rewrite Ec in RC. destruct RC as [Hc _]. auto.
  Qed.

  Lemma struct_not_mont : forall r a x, ref_at st OW PL r a -> a <= x < a + 24 -> mont_fp PL x -> False.
  Proof.
    parts.
    intros r a x HA Hx [(am & qm & Em & Hm)|(c & Ec & Hm)].
    2:{ pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
        destruct (recp_frame c Ec) as (Cc & Sc & Uc & Pc). unfold RECP_SC_SZ in *.
        destruct (skind_range r a K) as [(C1 & I1 & P1)|[[C1 U1]|[-> ->]]]; [lia| | unfold CONST_ONE in *; lia].
        destruct K as [q n S Eb Hin Hn|am qm M Em Hinm Ea Hoff|i qi H Er Eq Hini Ea Hj|p S Eb Hiv HF|Er Ea];
          [exfalso; destruct (sk_block_own _ _ _ _ Eb Hin Hn); lia
          | exfalso; destruct (sk_block_mont am qm a Hinm ltac:(right; exact I) ltac:(lia) ltac:(unfold MONT_CTX_SZ in *; lia)); lia
          | exfalso; destruct (sk_block_pool _ _ _ _ Hini Ea Hj); lia | | exfalso; subst; unfold CONST_ONE in *; lia].
        pose proof (proj2 (proj2 PWF)) as RC. rewrite Ec in RC. destruct RC as [_ AP].
        specialize (AP r p _ Eb Hiv). unfold iv_apart, BN_STRUCT_SZ, RECP_SC_SZ in AP. cbn [fst snd] in AP. lia. }
    pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K. pose proof (ids_m_nodup _ _ _ IDS) as NDm.
    pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR. destruct PLB as (PB & PC & PM). rewrite Em in PM.
    destruct (skind_range r a K) as [(C1 & I1 & P1)|[[C1 U1]|[-> ->]]].
    2:{ pose proof (blk_below_ceiling qm am MONT_CTX_SZ x PM ltac:(unfold MONT_CTX_SZ in *; lia)). lia. }
    2:{ pose proof (AH_range _ _ _ _ _ _ _ HEAP PM) as (_ & _ & _ & _ & BI). unfold CONST_ONE, MONT_CTX_SZ in *. lia. }
    destruct K as [q n S Eb Hin Hn|am' qm' M Em' Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea];
      [| | | exfalso; destruct (sk_frame a HF); lia| exfalso; subst; unfold CONST_ONE in *; lia]; unfold BN_STRUCT_SZ, MONT_CTX_SZ in *.
    - eapply (blk_excl q a n qm am 96 x Hin PM); [| lia| lia]. eapply ids_bn_mont_neq; eauto. exact (proj1 S).
    - rewrite Em in Em'. injection Em' as <- <-. lia.
    - eapply (blk_excl q H ITEM_SZ qm am 96 x Hin PM); [| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; nia| lia].
      intros ->. eapply (ids_pl_m st PL EA qm qm IDS); [eapply in_pl_ids_mont; exact Em| apply item_in_m; eapply nth_error_In; exact Eq| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma cx_not_mont : forall x, cx_fp st OW PL x -> mont_fp PL x -> False.
  Proof.
    parts.
    intros x HC [(am & qm & Em & Hm)|(c & Ec & Hm)].
    2:{ destruct (recp_frame c Ec) as (Cc & _). destruct (cx_fp_block x HC) as (q & A & n & Hin & Hxb & _).
        pose proof (blk_below_ceiling q A n x Hin Hxb). lia. }
    pose proof (ids_m_nodup _ _ _ IDS) as NDm. destruct PLB as (PB & PC & PM). rewrite Em in PM. unfold MONT_CTX_SZ in *.
    destruct HC as [(ac & qc & Ec & Hc)|[(q' & H' & Hq' & Hin' & Hc)|(q' & I & Eq' & Hin' & Hc)]].
    - rewrite Ec in PC. eapply (blk_excl qc ac BN_CTX_SZ qm am 96 x PC PM); [| exact Hc| lia]. eapply ids_ctx_mont_neq; eauto.
    - eapply (blk_excl q' H' ITEM_SZ qm am 96 x Hin' PM); [| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia| lia].
      intros ->. eapply (ids_pl_m st PL EA qm qm IDS); [eapply in_pl_ids_mont; exact Em| apply item_in_m; exact Hq'| reflexivity].
    - eapply (blk_excl q' I FRAMES_SZ qm am 96 x Hin' PM); [| exact Hc| lia].
      intros ->. eapply (ids_pl_m st PL EA qm qm IDS); [eapply in_pl_ids_mont; exact Em| apply idx_in_m; exact Eq'| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma limbs_not_cx : forall r p D x, vref r st -> bn_d (getbn r st) = Some p ->
    In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) OW -> D <= x < D + 8 * Z.of_nat (bn_dmax (getbn r st)) -> cx_fp st OW PL x -> False.
  Proof.
    parts.
    intros r p D x HV Ed Hin Hx HC.
    pose proof (bn_in_m r st p HV Ed) as Hm. pose proof (ids_m_nodup _ _ _ IDS) as NDm.
    destruct HC as [(ac & qc & Ec & Hc)|[(q' & H' & Hq' & Hin' & Hc)|(q' & I & Eq' & Hin' & Hc)]].
    - destruct PLB as (_ & PC & _). rewrite Ec in PC. eapply (blk_excl p D _ qc ac BN_CTX_SZ x Hin PC); [| exact Hx| exact Hc].
      intros ->. eapply (ids_pl_m st PL EA qc qc IDS); [eapply in_pl_ids_ctx; exact Ec| exact Hm| reflexivity].
    - eapply (blk_excl p D _ q' H' ITEM_SZ x Hin Hin'); [| exact Hx| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia]. eapply (ids_bn_item_neq r st p q'); eauto.
    - eapply (blk_excl p D _ q' I FRAMES_SZ x Hin Hin'); [| exact Hx| exact Hc]. eapply (ids_bn_idx_neq r st p q'); eauto.
  Qed.

  Lemma limbs_not_mont : forall r p D x, vref r st -> bn_d (getbn r st) = Some p ->
    In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) OW -> D <= x < D + 8 * Z.of_nat (bn_dmax (getbn r st)) -> mont_fp PL x -> False.
  Proof.
    parts.
    intros r p D x HV Ed Hin Hx [(am & qm & Em & Hm)|(c & Ec & Hm)].
    2:{ destruct (recp_frame c Ec) as (Cc & _). pose proof (blk_below_ceiling p D _ x Hin Hx). lia. }
    pose proof (bn_in_m r st p HV Ed) as Hmm.
    destruct PLB as (_ & _ & PM). rewrite Em in PM. eapply (blk_excl p D _ qm am MONT_CTX_SZ x Hin PM); [| exact Hx| unfold MONT_CTX_SZ in *; lia].
    intros ->. eapply (ids_pl_m st PL EA qm qm IDS); [eapply in_pl_ids_mont; exact Em| exact Hmm| reflexivity].
  Qed.

  (* [comment removed for export] *)
  Lemma framebuf_not_mont : forall r y d x, pl_bn PL r = Some (PFrameBuf y d) -> d <= x < d + TMOD_BUF_SZ -> mont_fp PL x -> False.
  Proof.
    parts.
    intros r y d x Eb Hx HM. pose proof (pl_wf_stored PL r _ PWF Eb) as S. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
    assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
    { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
    destruct (frame_iv_range _ HFd) as (Cd & _ & _). cbn [fst] in Cd.
    destruct HM as [(am & qm & Em & Hm)|(c & Ec & Hm)].
    - destruct PLB as (_ & _ & PM). rewrite Em in PM. pose proof (blk_below_ceiling qm am MONT_CTX_SZ x PM ltac:(unfold MONT_CTX_SZ in *; lia)). lia.
    - pose proof (proj2 (proj2 PWF)) as RC. rewrite Ec in RC. destruct RC as [_ AP].
      specialize (AP r _ (d, d + TMOD_BUF_SZ) Eb ltac:(right; left; reflexivity)). unfold iv_apart, TMOD_BUF_SZ, RECP_SC_SZ in *. cbn [fst snd] in AP. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma err_not_block : forall q A n x, In (q, A, n) OW -> A <= x < A + n -> (forall q', In q' (ApBnRepA.ea_ids EA) -> q <> q') -> ApBnRepA.err_fp OW EA x -> False.
  Proof.
    parts.
    intros q A n x Hin Hxb NEe He. unfold ApBnRepA.err_fp, in_block in He. destruct He as ([[q' A'] n'] & Hb & Hx). cbn [blk_addr blk_size fst snd] in Hx.
    eapply (blk_excl q A n q' A' n' x Hin (ERRB _ ltac:(apply in_or_app; left; exact Hb))); [| exact Hxb| exact Hx].
    apply NEe. eapply ApBnRepA.ea_ids_blk. exact Hb.
  Qed.

  (* [comment removed for export] *)
  Lemma err_below_ceiling : forall x, ApBnRepA.err_fp OW EA x -> x < ACEIL /\ (x < 0x10000 \/ 0xbcb000 <= x).
  Proof.
    parts.
    intros x He. unfold ApBnRepA.err_fp, in_block in He. destruct He as ([[q A] n] & Hb & Hx). cbn [blk_addr blk_size fst snd] in Hx.
    pose proof (AH_range _ _ _ _ _ _ _ HEAP (ERRB _ ltac:(apply in_or_app; left; exact Hb))). unfold ablock_range in *; lia.
  Qed.

  Lemma own_fp_not_struct : forall cxo hs x r a, In r hs -> ref_at st OW PL r a -> r <> ROne -> own_fpc cxo hs st OW PL EA x -> a <= x < a + 24 -> False.
  Proof.
    parts.
    intros cxo hs x r a Hr HA HNO HO Hx. pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
    destruct HO as [HL|[(r' & a' & HA' & HV' & Hn' & [Hs|[(p' & D' & Ed' & Hin' & Hx')|(y & d & Ep & Hx')]])|[[_ HC]|[HMo|He]]]].
    - destruct (skind_range r a K) as [(C1 & I1 & P1)|[[C1 U1]|[-> ->]]]; [| | exact (HNO eq_refl)].
      + destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea];
          [eapply (blk_not_libw q a n); eauto; unfold BN_STRUCT_SZ in *; lia
          | eapply (blk_not_libw qm am MONT_CTX_SZ); eauto; unfold MONT_CTX_SZ in *; lia
          | eapply (blk_not_libw q H ITEM_SZ); eauto; unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; nia
          | destruct (sk_frame a HF); lia | subst; exact (HNO eq_refl)].
      + revert HL. unfold libw, LIBW_bgr, ARun.LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. clia.
    - assert (NE : r <> r') by (intros ->; contradiction). pose proof (struct_disj r r' a a' NE HA HA'). lia.
    - pose proof (struct_limbs_disj r r' a p' D' _ HA HV' Ed' Hin'). lia.
    - destruct (pl_of_cases PL r' _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S' Eb']]]; [discriminate E'| discriminate E'|].
      pose proof (framebuf_struct_disj r' y d r a Eb' HA). unfold TMOD_BUF_SZ in *. lia.
    - eapply struct_not_cx; eauto.
    - eapply struct_not_mont; eauto.
    - destruct (skind_range r a K) as [(C1 & I1 & P1)|[[C1 U1]|[-> ->]]]; [| destruct (err_below_ceiling x He); lia| exact (HNO eq_refl)].
      destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea];
        [| | | destruct (sk_frame a HF); lia| subst; exact (HNO eq_refl)]; unfold BN_STRUCT_SZ, MONT_CTX_SZ in *.
      + eapply (err_not_block q a n x Hin); [lia| | exact He]. intros q' Hq'. eapply ids_pl_ea; eauto. eapply in_pl_ids_bn; [exact (proj1 S)| exact Eb].
      + eapply (err_not_block qm am 96 x Hin); [lia| | exact He]. intros q' Hq'. eapply ids_pl_ea; eauto. eapply in_pl_ids_mont; exact Em.
      + eapply (err_not_block q H ITEM_SZ x Hin); [unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; nia| | exact He].
        intros q' Hq' ->. eapply (ids_ea_m st PL EA q' q' IDS); [exact Hq'| apply item_in_m; eapply nth_error_In; exact Eq| reflexivity].
  Qed.

  Lemma own_fp_not_limbs : forall cxo hs x r p D, In r hs -> vref r st -> bn_d (getbn r st) = Some p ->
    In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) OW -> own_fpc cxo hs st OW PL EA x ->
    D <= x < D + 8 * Z.of_nat (bn_dmax (getbn r st)) -> False.
  Proof.
    parts.
    intros cxo hs x r p D Hr HV Ed Hin HO Hx.
    pose proof (bn_in_m r st p HV Ed) as Hm. pose proof (ids_m_nodup _ _ _ IDS) as NDm.
    destruct HO as [HL|[(r' & a' & HA' & HV' & Hn' & [Hs|[(p' & D' & Ed' & Hin' & Hx')|(y & d & Ep & Hx')]])|[[_ HC]|[HMo|He]]]].
    - eapply blk_not_libw; eauto.
    - pose proof (struct_limbs_disj r' r a' p D _ HA' HV Ed Hin). lia.
    - assert (NE : r <> r') by (intros ->; contradiction).
      pose proof (limbs_limbs_disj r r' p D _ p' D' _ NE HV HV' Ed Ed' Hin Hin'). lia.
    - destruct (pl_of_cases PL r' _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S' Eb']]]; [discriminate E'| discriminate E'|].
      assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
      { apply pl_frames_In. left. exists r'. rewrite Eb'. split; [exact (proj1 S')| right; left; reflexivity]. }
      destruct (frame_iv_range _ HFd) as (Cd & _ & _). cbn [fst] in Cd. pose proof (blk_below_ceiling p D _ x Hin Hx). lia.
    - eapply limbs_not_cx; eauto.
    - eapply limbs_not_mont; eauto.
    - eapply (err_not_block p D _ x Hin Hx); [|exact He]. intros q' Hq' E. subst q'. eapply (ids_ea_m st PL EA p p IDS); eauto.
  Qed.

  Lemma own_fp_not_cx : forall hs x, own_fpc true hs st OW PL EA x -> cx_fp st OW PL x -> False.
  Proof.
    parts.
    intros hs x HO HC.
    destruct HO as [HL|[(r' & a' & HA' & HV' & Hn' & [Hs|[(p' & D' & Ed' & Hin' & Hx')|(y & d & Ep & Hx')]])|[[Ec _]|[HMo|He]]]]; [| | | |discriminate| |].
    - destruct (cx_fp_block x HC) as (q & A & n & Hin & Hxb & _). eapply blk_not_libw; eauto.
    - eapply struct_not_cx; eauto.
    - eapply limbs_not_cx; eauto.
    - destruct (pl_of_cases PL r' _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S' Eb']]]; [discriminate E'| discriminate E'|].
      assert (HFd : In (d, d + TMOD_BUF_SZ) (pl_frames PL)).
      { apply pl_frames_In. left. exists r'. rewrite Eb'. split; [exact (proj1 S')| right; left; reflexivity]. }
      destruct (frame_iv_range _ HFd) as (Cd & _ & _). cbn [fst] in Cd.
      destruct (cx_fp_block x HC) as (q & A & n & Hin & Hxb & _). pose proof (blk_below_ceiling q A n x Hin Hxb). lia.
    - eapply cx_not_mont; eauto.
    - destruct (cx_fp_block x HC) as (q & A & n & Hin & Hxb & Hq).
      eapply (err_not_block q A n x Hin Hxb); [|exact He]. intros q' Hq' E. subst q'.
      unfold all_ids in Hq. rewrite !in_app_iff in Hq. destruct Hq as [Hq|[Hq|Hq]].
      + eapply (ids_pl_ea st PL EA q q IDS); eauto.
      + (* [comment removed for export] *)
        pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
        (* [comment removed for export] *)
        destruct HC as [(ac & qc & Ec' & Hc)|[(q'' & H' & Hq'' & Hin' & Hc)|(q'' & I & Eq'' & Hin' & Hc)]].
        * destruct PLB as (_ & PC & _). rewrite Ec' in PC.
          destruct (decide (q = qc)) as [->|NE]; [eapply (ids_pl_ea st PL EA qc qc IDS); [eapply in_pl_ids_ctx; exact Ec'| exact Hq| reflexivity]|].
          eapply (blk_excl q A n qc ac BN_CTX_SZ x Hin PC NE Hxb Hc).
        * destruct (decide (q = q'')) as [->|NE]; [eapply (ids_ea_m st PL EA q'' q'' IDS); [exact Hq| apply item_in_m; exact Hq''| reflexivity]|].
          eapply (blk_excl q A n q'' H' ITEM_SZ x Hin Hin' NE Hxb). unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia.
        * destruct (decide (q = q'')) as [->|NE]; [eapply (ids_ea_m st PL EA q'' q'' IDS); [exact Hq| apply idx_in_m; exact Eq''| reflexivity]|].
          eapply (blk_excl q A n q'' I FRAMES_SZ x Hin Hin' NE Hxb Hc).
      + eapply (ids_ea_m st PL EA q q IDS); eauto.
  Qed.

  (* [comment removed for export] *)
  Theorem own_fp_outside : forall cxo hs W x, Forall (w_okc cxo hs) W -> own_fpc cxo hs st OW PL EA x -> outside W x.
  Proof.
    parts.
    intros cxo hs W x HW HO. induction HW as [|[lo hi] W Hiv HW IH]; [exact I|]. cbn [outside]. split; [|exact IH].
    intros Hx. cbn [fst snd] in *. destruct Hiv as [Hs Hsp|r a Hr HA HNO H1 H2|r p D Hr HV Ed Hin H1 H2|q A n Hin Hq H1 H2|Ec Hcx]; cbn [fst snd] in *.
    - destruct (own_fp_block cxo hs x HO) as [HL|[(q & A & n & Hin & Hxb & _)|(iv & Hiv & Hxi)]].
      + revert HL. unfold libw, LIBW_bgr, ARun.LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. clia.
      + pose proof (blk_below_ceiling q A n x Hin Hxb). lia.
      + destruct (frame_iv_range _ Hiv) as (_ & S2 & _). lia.
    - eapply (own_fp_not_struct cxo hs x r a); eauto. lia.
    - eapply (own_fp_not_limbs cxo hs x r p D); eauto. lia.
    - destruct (own_fp_block cxo hs x HO) as [HL|[(q' & A' & n' & Hin' & Hxb' & Hq')|(iv & Hiv & Hxi)]].
      + pose proof (AH_range_gen _ _ _ _ _ HEAP Hin) as (_ & _ & _ & _ & BI). cbn [blk_addr blk_size fst snd] in BI.
        revert HL. unfold libw, LIBW_bgr, ARun.LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia.
      + assert (NE : q' <> q) by (intros ->; contradiction).
        pose proof (AH_disjoint_gen _ _ _ _ (q', A', n') (q, A, n) HEAP ltac:(apply in_or_app; left; exact Hin') Hin NE) as DJ.
        cbn [blk_addr blk_size fst snd] in DJ. lia.
      + pose proof (AH_range_gen _ _ _ _ _ HEAP Hin) as (_ & _ & _ & BC & _). cbn [blk_addr blk_size fst snd] in BC.
        destruct (frame_iv_range _ Hiv) as (S1 & _ & _). lia.
    - subst cxo. eapply own_fp_not_cx; [exact HO| apply Hcx; exact Hx].
  Qed.

End Disj.
End WithCeiling2.
Notation w_ok OW LB st PL EA SPX := (w_okc OW LB st PL EA SPX false).

(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithCeiling3. Context {AR : ARun}.
Local Notation RT := (@ar_RT AR).
Local Notation AF := (@ar_AF AR).
Local Notation SP0 := (@ar_SP0 AR).
Local Notation LIBW_cs := (@ar_LIBW_cs AR).
Local Notation ACEIL := (@BnHeapA.ACEIL AR).
Local Notation AHEAP := (@BnHeapA.AHEAP AR).

Lemma lib_state_h_parts : forall cxo hs s m OW PL EA, lib_state_hc cxo hs s m OW PL EA -> lib_parts s OW PL EA.
Proof.
  intros cxo hs s m OW PL EA (_ & (_ & (_ & EB)) & _ & (S1 & S2 & S3 & HM)).
  split; [exact S1|]. split; [exact S2|]. split; [exact S3|]. split; [eapply gen_parts; exact HM|]. exact EB.
Qed.

Lemma lib_state_wf : forall cxo hs s m OW PL EA, lib_state_hc cxo hs s m OW PL EA -> st_wf s.
Proof. intros cxo hs s m OW PL EA (_ & _ & _ & (S1 & _)). exact S1. Qed.

(* [comment removed for export] *)
Theorem lib_state_frame : forall s LB SPX BX cxo hs st m m' OW PL EA W,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> munch W m m' -> wmono ctasegs m m' -> frames_ok PL SPX BX ->
  Forall (w_okc OW LB st PL EA SPX cxo hs) W -> lib_state_hc cxo hs st m' OW PL EA.
Proof.
  intros s LB SPX BX cxo hs st m m' OW PL EA W HEAP HS MU WM FROK HW.
  pose proof (lib_state_h_parts _ _ _ _ _ _ _ HS) as PARTS.
  eapply lib_state_hc_agree; [exact HS|]. eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|].
  intros a Ha. eapply own_fp_outside; eauto.
Qed.

(* [comment removed for export] *)
Theorem lib_state_h_ow : forall cxo hs s m OW OW' PL EA,
  lib_state_hc cxo hs s m OW PL EA ->
  (forall q A n, In q (all_ids s PL EA) -> In (q, A, n) OW -> In (q, A, n) OW') ->
  lib_state_hc cxo hs s m OW' PL EA.
Proof.
  intros cxo hs s m OW OW' PL EA HS HOW. pose proof HS as (HC & (HE1 & HE2) & HO & (S1 & S2 & S3 & HM)).
  unfold all_ids in HOW.
  assert (HPL : forall q A n, In q (pl_ids PL) -> In (q, A, n) OW -> In (q, A, n) OW') by (intros q A n Hq; apply HOW; apply in_or_app; left; exact Hq).
  assert (HMI : forall q A n, In q (map fst (blocks_of s)) -> In (q, A, n) OW -> In (q, A, n) OW')
    by (intros q A n Hq; apply HOW; apply in_or_app; right; apply in_or_app; right; exact Hq).
  split; [exact HC|]. split.
  { split; [exact HE1|]. eapply ApBnRepA.err_mem_agree; [apply agree_on_refl| intros a Ha; exact I| intros x Hx; exact I| | exact HE2].
    intros q A n Hq. apply HOW. apply in_or_app; right; apply in_or_app; left; exact Hq. }
  split; [exact HO|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply (gen_transport (fun _ => True)); [exact HM| apply agree_on_refl| auto| | | | | | auto|].
  - intros ac qc Ec Hin. apply HPL; [eapply in_pl_ids_ctx; exact Ec| exact Hin].
  - intros q H Hq Hin. apply HMI; [apply item_in_m; exact Hq| exact Hin].
  - intros q I Eq Hin. apply HMI; [apply idx_in_m; exact Eq| exact Hin].
  - intros am qm Em Hin. apply HPL; [eapply in_pl_ids_mont; exact Em| exact Hin].
  - intros r p Hr E OK. destruct p as [a q off|a|a d|a]; try exact OK. destruct OK as (n & Hin & H1 & H2). exists n. split; [|lia].
    destruct (pl_of_cases PL r _ E) as [[_ E']|[(am & qm & M & Em & E' & _)|[S Eb]]]; [discriminate E'| |].
    + injection E' as Ea Eq Eo. subst q. apply HPL; [eapply in_pl_ids_mont; exact Em| exact Hin].
    + apply HPL; [eapply in_pl_ids_bn; [exact Hr| exact Eb]| exact Hin].
  - intros r a HA [Hh|HR]; [left; exact Hh|]. right.
    eapply (bn_rep_transport (fun _ => True)); [apply agree_on_refl| auto| | exact HR].
    intros p D Ed Hin. apply HMI; [eapply bn_in_m; [eapply gen_ref_valid; eauto| exact Ed]| exact Hin].
Qed.

Lemma lib_state_h_incl : forall cxo hs hs' s m OW PL EA,
  lib_state_hc cxo hs s m OW PL EA -> (forall r, In r hs -> In r hs') -> lib_state_hc cxo hs' s m OW PL EA.
Proof.
  intros cxo hs hs' s m OW PL EA (HC & HE & HO & (S1 & S2 & S3 & HM)) Hi.
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply gen_impl; [|exact HM]. intros a b r [Hh|HR]; [left; apply Hi; exact Hh| right; exact HR].
Qed.

Lemma ref_at_fun : forall s OW PL r a a', List.NoDup (map blk_id OW) -> ref_at s OW PL r a -> ref_at s OW PL r a' -> a = a'.
Proof.
  intros s OW PL r a a' ND H1 H2. unfold ref_at in H1, H2. destruct (r <? NFIX)%nat.
  - destruct H1 as (p1 & E1 & <-), H2 as (p2 & E2 & <-). rewrite E1 in E2. injection E2 as <-. reflexivity.
  - destruct H1 as (p1 & A1 & E1 & I1 & ->), H2 as (p2 & A2 & E2 & I2 & ->). rewrite E1 in E2. injection E2 as <-.
    destruct (AH_addr_unique OW p1 A1 ITEM_SZ A2 ITEM_SZ ND I1 I2) as [-> _]. reflexivity.
Qed.

Lemma ref_at_valid : forall cxo hs s m OW PL EA r a, lib_state_hc cxo hs s m OW PL EA -> ref_at s OW PL r a -> vref r s.
Proof. intros cxo hs s m OW PL EA r a (_ & _ & _ & (S1 & _ & _ & HM)) HA. eapply gen_ref_valid; eauto. Qed.

(* [comment removed for export] *)
Definition bn_rep_rw (m : mem) (OW : list block) (pl : option place) (a : Z) (b : BN) : Prop :=
  exists D, rw_cells ctasegs m a (bn_cells D b) /\ bn_arr m OW pl D b.
Definition bn_rep_ro (m : mem) (OW : list block) (pl : option place) (a : Z) (b : BN) : Prop :=
  exists D, ro_cells ctasegs m a (bn_cells D b) /\ bn_arr m OW pl D b.

Lemma bn_rep_rw_of : forall m OW PL r a b, pl_wf PL -> r <> ROne -> bn_rep m OW (pl_of PL r) a b -> bn_rep_rw m OW (pl_of PL r) a b.
Proof.
  intros m OW PL r a b WF NE (D & HC & HA). exists D. split; [|exact HA]. unfold struct_cells in HC.
  destruct (pl_of PL r) as [p|] eqn:E; [|exact HC]. destruct p; try exact HC.
  exfalso. destruct (pl_of_cases PL r _ E) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
  exact (proj2 (proj2 (proj2 (proj1 WF r _ Eb)))).
Qed.

Lemma bn_rep_of_rw : forall m OW PL r a b, pl_wf PL -> r <> ROne -> bn_rep_rw m OW (pl_of PL r) a b -> bn_rep m OW (pl_of PL r) a b.   (* [comment removed for export] *)
Proof.
  intros m OW PL r a b WF NE (D & HC & HA). exists D. split; [|exact HA]. unfold struct_cells.
  destruct (pl_of PL r) as [p|] eqn:E; [|exact HC]. destruct p; try exact HC.
  exfalso. destruct (pl_of_cases PL r _ E) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
  exact (proj2 (proj2 (proj2 (proj1 WF r _ Eb)))).
Qed.

Lemma bn_rep_ro_of : forall m OW pl a b, bn_rep m OW pl a b -> const_one_cells m -> bn_rep_ro m OW pl a b.   (* [comment removed for export] *)
Proof.
  intros m OW pl a b (D & HC & HA) HONE. exists D. split; [|exact HA]. unfold struct_cells in HC. destruct pl as [[| | |]|]; try exact (proj1 HC); try exact HC.
  destruct HC as [-> E]. rewrite E. exact HONE.
Qed.

(* [comment removed for export] *)
Theorem lib_state_open : forall cxo hs s m OW PL EA r a,
  lib_state_hc cxo hs s m OW PL EA -> List.NoDup (map blk_id OW) -> ref_at s OW PL r a -> ~ In r hs -> r <> ROne ->
  bn_rep_rw m OW (pl_of PL r) a (getbn r s) /\ bg_ok (getbn r s) /\ lib_state_hc cxo (r :: hs) s m OW PL EA.
Proof.
  intros cxo hs s m OW PL EA r a HS ND HA Hn NE. pose proof (ref_at_valid _ _ _ _ _ _ _ _ _ HS HA) as HV.
  pose proof HS as (_ & _ & _ & (S1 & S2 & _ & HM)).
  split; [|split].
  - destruct (gen_get _ _ _ _ _ _ _ _ HM ND HA) as [Hh|HR]; [contradiction|]. apply bn_rep_rw_of; assumption.
  - apply st_wf_ok; assumption.
  - eapply lib_state_h_incl; [exact HS|]. intros r' Hr'. right. exact Hr'.
Qed.

(* [comment removed for export] *)
Theorem lib_state_open_ro : forall cxo hs s m OW PL EA r a,
  lib_state_hc cxo hs s m OW PL EA -> List.NoDup (map blk_id OW) -> ref_at s OW PL r a -> ~ In r hs -> const_one_cells m ->     (* [comment removed for export] *)
  bn_rep_ro m OW (pl_of PL r) a (getbn r s) /\ bg_okv (getbn r s) /\ bn_rep m OW (pl_of PL r) a (getbn r s) /\ lib_state_hc cxo (r :: hs) s m OW PL EA.
Proof.
  intros cxo hs s m OW PL EA r a HS ND HA Hn HONE. pose proof (ref_at_valid _ _ _ _ _ _ _ _ _ HS HA) as HV.
  pose proof HS as (_ & _ & _ & (S1 & S2 & _ & HM)).
  destruct (gen_get _ _ _ _ _ _ _ _ HM ND HA) as [Hh|HR]; [contradiction|].
  split; [apply bn_rep_ro_of; [exact HR| exact HONE]|]. split; [apply st_wf_okv; assumption|]. split; [exact HR|].
  eapply lib_state_h_incl; [exact HS|]. intros r' Hr'. right. exact Hr'.
Qed.

(* [comment removed for export] *)
Theorem lib_state_close : forall cxo hs s m OW PL EA r a b',
  lib_state_hc cxo (r :: hs) s m OW PL EA -> List.NoDup (map blk_id OW) -> ref_at s OW PL r a -> r <> ROne ->
  bn_rep_rw m OW (pl_of PL r) a b' -> bg_ok b' -> ids_ok (setbn r b' s) PL EA ->
  lib_state_hc cxo hs (setbn r b' s) m OW PL EA.
Proof.
  intros cxo hs s m OW PL EA r a b' HS ND HA NE HR HOK HIDS. pose proof (ref_at_valid _ _ _ _ _ _ _ _ _ HS HA) as HV.
  destruct HS as (HC & HE & HO & (S1 & S2 & S3 & HM)).
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|].
  split; [apply st_wf_setbn; assumption|]. split; [exact S2|]. split; [exact HIDS|].
  apply (bn_rep_of_rw m OW PL r a b' S2 NE) in HR.
  assert (HM2 : bn_mem_gen (holeR (r :: hs) m OW PL) cxo (setbn r b' s) m OW PL) by (eapply gen_set; [exact HM| exact ND| exact HA| exact HV| right; exact HR]).
  (* [comment removed for export] *)
  eapply (gen_transport (fun _ => True) (holeR (r :: hs) m OW PL) (holeR hs m OW PL)); [exact HM2| apply agree_on_refl| auto| auto| auto| auto| auto| auto| auto|].
  intros r' a' HA' [Hh|HR']; [|right; exact HR'].
  destruct Hh as [<-|Hh]; [|left; exact Hh]. right.
  apply ref_at_setbn in HA'. rewrite (ref_at_fun _ _ _ _ _ _ ND HA' HA). rewrite getbn_setbn_same by exact HV. exact HR.
Qed.

(* [comment removed for export] *)
Theorem lib_state_reclose : forall cxo hs s m OW PL EA r a,
  lib_state_hc cxo (r :: hs) s m OW PL EA -> List.NoDup (map blk_id OW) -> ref_at s OW PL r a ->
  bn_rep m OW (pl_of PL r) a (getbn r s) -> lib_state_hc cxo hs s m OW PL EA.
Proof.
  intros cxo hs s m OW PL EA r a HS ND HA HR.
  destruct HS as (HC & HE & HO & (S1 & S2 & S3 & HM)).
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply (gen_transport (fun _ => True) (holeR (r :: hs) m OW PL) (holeR hs m OW PL)); [exact HM| apply agree_on_refl| auto| auto| auto| auto| auto| auto| auto|].
  intros r' a' HA' [Hh|HR']; [|right; exact HR'].
  destruct Hh as [<-|Hh]; [|left; exact Hh]. right. rewrite (ref_at_fun _ _ _ _ _ _ ND HA' HA). exact HR.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cx_view (m : mem) (OW : list block) (PL : placement) (s : ST) (Hs : list Z) (I : Z) : Prop :=
  match pl_ctx PL with
  | None => st_ctx s = gx_nil /\ skipn NFIX (st_bns s) = [] /\ Hs = []
  | Some (ac, qc) =>
      In (qc, ac, BN_CTX_SZ) OW /\ length Hs = length (gx_items (st_ctx s))
      /\ rw_cells ctasegs m ac (ctx_cells (hd 0 Hs) (cur_addr Hs (st_ctx s)) (last Hs 0) I (st_ctx s))
      /\ stack_rep m OW I (st_ctx s)
      /\ (forall k q, nth_error (gx_items (st_ctx s)) k = Some q -> In (q, nth k Hs 0, ITEM_SZ) OW)
      /\ (forall k H, nth_error Hs k = Some H ->
            rw_cells ctasegs m (H + 384) [C8 (wz (match k with O => 0 | S k' => nth k' Hs 0 end)); C8 (wz (nth (S k) Hs 0))])
  end.
(* [comment removed for export] *)
Lemma items_gen_Hs_of_blocks : forall R cxo m OW items Hs0 vals k0 prev Hs,
  items_gen R cxo m OW items Hs0 vals k0 prev -> List.NoDup (map blk_id OW) -> length Hs = length items ->
  (forall k q, nth_error items k = Some q -> In (q, nth k Hs 0, ITEM_SZ) OW) -> Hs0 = Hs.
Proof.
  intros R cxo m OW items. induction items as [|q items IH]; intros Hs0 vals k0 prev Hs HIT ND LHs HItems;
    destruct Hs0 as [|H0 Hs0]; destruct Hs as [|H Hs]; cbn [items_gen length] in HIT, LHs; try contradiction; try lia; [reflexivity|].
  destruct HIT as (Hin & _ & _ & _ & HIT).
  pose proof (HItems 0%nat q eq_refl) as Hin'. cbn [nth] in Hin'. destruct (AH_addr_unique OW q H0 ITEM_SZ H ITEM_SZ ND Hin Hin') as [-> _]. f_equal.
  eapply (IH Hs0 _ _ _ Hs); [exact HIT| exact ND| lia|]. intros k q' Hk. exact (HItems (S k) q' Hk).
Qed.

(* [comment removed for export] *)
Theorem lib_state_cx_open : forall hs s m OW PL EA,
  lib_state_hc false hs s m OW PL EA ->
  exists Hs Ia, cx_view m OW PL s Hs Ia /\ lib_state_hc true hs s m OW PL EA.
Proof.
  intros hs s m OW PL EA (HC & HE & HO & (S1 & S2 & S3 & (HF & HN & HCX & HM))). pose proof HM as HM'.
  unfold lib_state_hc, bn_state_hc, bn_mem_gen, cx_view. destruct (pl_ctx PL) as [[ac qc]|].
  - destruct HCX as (Hinc & Hs & I & LHs & HCe & HIT). destruct (HCe eq_refl) as [HCe1 HSt]. exists Hs, I.
    split.
    { split; [exact Hinc|]. split; [exact LHs|]. split; [exact HCe1|]. split; [exact HSt|]. split.
      - intros k q Hk. destruct (items_gen_nth _ _ _ _ _ _ _ _ _ _ _ HIT Hk) as (H & HH & Hin & _). rewrite (nth_error_nth _ _ _ HH). exact Hin.
      - intros k H Hk. exact (items_gen_links _ _ _ _ _ _ _ _ _ _ HIT Hk). }
    split; [exact HC|]. split; [exact HE|]. split; [exact HO|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
    split; [exact HF|]. split; [exact HN|]. split; [|exact HM'].
    split; [exact Hinc|]. exists Hs, I. split; [exact LHs|]. split; [intros E; discriminate E|]. eapply items_gen_open. exact HIT.
  - exists [], 0. destruct HCX as [E1 E2]. split; [auto|].
    split; [exact HC|]. split; [exact HE|]. split; [exact HO|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
    split; [exact HF|]. split; [exact HN|]. split; [split; assumption| exact HM'].
Qed.

(* [comment removed for export] *)
Theorem lib_state_cx_close : forall hs s s' m OW PL EA Hs Ia,
  lib_state_hc true hs s m OW PL EA -> List.NoDup (map blk_id OW) ->
  st_bns s' = st_bns s -> gx_items (st_ctx s') = gx_items (st_ctx s) -> mont_cells s' = mont_cells s -> recp_cells s' = recp_cells s ->
  st_wf s' -> ids_ok s' PL EA ->
  cx_view m OW PL s' Hs Ia ->
  lib_state_hc false hs s' m OW PL EA.
Proof.
  intros hs s s' m OW PL EA Hs Ia (HC & HE & HO & (S1 & S2 & S3 & (HF & HN & HCX & HM))) ND EB EI EMC ERC WF' IDS' CV.
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|]. split; [exact WF'|]. split; [exact S2|]. split; [exact IDS'|].
  assert (EG : forall r, getbn r s' = getbn r s) by (intros r; unfold getbn; rewrite EB; reflexivity).
  split. { intros r p Hr E. destruct (HF r p Hr E) as [OK H]. split; [exact OK|]. rewrite EG. exact H. }
  split. { intros r Hr E. rewrite EG. apply HN; assumption. }
  split.
  - unfold cx_view in CV. destruct (pl_ctx PL) as [[ac qc]|].
    + destruct CV as (Hinc' & LHs & HCe & HSt & HItems & HLinks). destruct HCX as (Hinc & Hs0 & I0 & LHs0 & _ & HIT).
      split; [exact Hinc|]. exists Hs, Ia. split; [exact LHs|]. split; [intros _; split; assumption|].
      rewrite EB, EI. rewrite EI in LHs.
      assert (Hs0 = Hs) as <- by (eapply items_gen_Hs_of_blocks; [exact HIT| exact ND| exact LHs| rewrite EI in HItems; exact HItems]).
      eapply items_gen_close; [exact HIT|]. intros k H Hk. exact (HLinks k H Hk).
    + destruct CV as (E1 & E2 & _). split; assumption.
  - rewrite EMC, ERC. exact HM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nodup_insert : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> ~ In x (l1 ++ l2) -> List.NoDup (l1 ++ x :: l2).
Proof. intros A l1 l2 x ND Hn. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; assumption. Qed.

(* [comment removed for export] *)
Lemma ids_ok_setbn_same : forall s PL EA r b', ids_ok s PL EA -> vref r s -> bn_blocks b' = bn_blocks (getbn r s) -> ids_ok (setbn r b' s) PL EA.
Proof. intros s PL EA r b' H HV HBL. unfold ids_ok, all_ids in *. rewrite (blocks_of_setbn_same r b' s HV HBL). exact H. Qed.

(* [comment removed for export] *)
Lemma ids_ok_setbn_new : forall s PL EA r b' p', ids_ok s PL EA -> vref r s -> bn_d b' = Some p' -> ~ In p' (all_ids s PL EA) -> ids_ok (setbn r b' s) PL EA.
Proof.
  intros s PL EA r b' p' S3 HV Hd Hn. unfold ids_ok, all_ids in *. set (PIDS := pl_ids PL) in *. clearbody PIDS.
  destruct (blocks_setbn r s HV) as (R & P1 & P2). specialize (P2 b'). unfold bn_blocks at 1 in P2. rewrite Hd in P2. cbn [app] in P2.
  apply (Permutation_map fst) in P1. apply (Permutation_map fst) in P2. rewrite map_app in P1. cbn [map fst] in P2.
  assert (S4 : List.NoDup (PIDS ++ ApBnRepA.ea_ids EA ++ map fst (bn_blocks (getbn r s)) ++ map fst R)).
  { eapply Permutation_NoDup; [|exact S3]. apply Permutation_app_head. apply Permutation_app_head. exact P1. }
  assert (Hn4 : ~ In p' (PIDS ++ ApBnRepA.ea_ids EA ++ map fst (bn_blocks (getbn r s)) ++ map fst R)).
  { intros Hin. apply Hn. rewrite !in_app_iff in *. destruct Hin as [H|[H|H]]; [tauto| tauto|]. right; right.
    eapply Permutation_in; [apply Permutation_sym; exact P1|]. rewrite in_app_iff. exact H. }
  eapply Permutation_NoDup with (l := p' :: PIDS ++ ApBnRepA.ea_ids EA ++ map fst R).
  { eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head.
    eapply Permutation_trans; [apply Permutation_middle|]. apply Permutation_app_head. apply Permutation_sym. exact P2. }
  constructor.
  - intros Hin. apply Hn4. rewrite !in_app_iff in *. tauto.
  - rewrite !app_assoc in S4. clear - S4. rewrite <- !app_assoc in S4.
    revert S4. generalize PIDS (ApBnRepA.ea_ids EA) (map fst (bn_blocks (getbn r s))) (map fst R). clear.
    intros l1 l2 X l3 H. rewrite app_assoc in H. rewrite app_assoc.
    induction (l1 ++ l2) as [|x l IH]; cbn [app] in *; [eapply nodup_app_r; exact H|].
    apply NoDup_cons_iff in H. destruct H as [Hx H]. constructor; [|auto].
    intros Hin. apply Hx. rewrite !in_app_iff in *. tauto.
Qed.

(* [comment removed for export] *)
Lemma ids_ok_setbn_none : forall s PL EA r b', ids_ok s PL EA -> vref r s -> bn_d b' = None -> ids_ok (setbn r b' s) PL EA.
Proof.
  intros s PL EA r b' S3 HV Hd. unfold ids_ok, all_ids in *. rewrite app_assoc in S3 |- *. set (PIDS := pl_ids PL ++ ApBnRepA.ea_ids EA) in *. clearbody PIDS.
  destruct (blocks_setbn r s HV) as (R & P1 & P2). specialize (P2 b'). unfold bn_blocks at 1 in P2. rewrite Hd in P2. cbn [app] in P2.
  apply (Permutation_map fst) in P1. apply (Permutation_map fst) in P2. rewrite map_app in P1.
  eapply Permutation_NoDup; [apply Permutation_app_head; apply Permutation_sym; exact P2|].
  assert (S4 : List.NoDup (PIDS ++ map fst (bn_blocks (getbn r s)) ++ map fst R)).
  { eapply Permutation_NoDup; [|exact S3]. apply Permutation_app_head. exact P1. }
  clear - S4. revert S4. generalize PIDS (map fst (bn_blocks (getbn r s))) (map fst R). clear.
  intros l1 X l3 H. induction l1 as [|x l IH]; cbn [app] in *; [eapply nodup_app_r; exact H|].
  apply NoDup_cons_iff in H. destruct H as [Hx H]. constructor; [|auto]. intros Hin. apply Hx. rewrite !in_app_iff in *. tauto.
Qed.

(* [comment removed for export] *)
Lemma ids_ok_set_ctx_same : forall s PL EA c', ids_ok s PL EA ->
  gx_items c' = gx_items (st_ctx s) -> gx_indexes c' = gx_indexes (st_ctx s) -> ids_ok (set_ctx c' s) PL EA.
Proof. intros s PL EA c' H E1 E2. unfold ids_ok, all_ids, blocks_of in *. cbn [set_ctx st_bns st_ctx]. rewrite E1, E2. exact H. Qed.

(* [comment removed for export] *)
Lemma ids_ok_set_ctx_new_idx : forall s PL EA c' q, ids_ok s PL EA ->
  gx_items c' = gx_items (st_ctx s) -> gx_indexes (st_ctx s) = None -> gx_indexes c' = Some q ->
  ~ In q (all_ids s PL EA) -> ids_ok (set_ctx c' s) PL EA.
Proof.
  intros s PL EA c' q H E1 EN EQ Hn. unfold ids_ok, all_ids, blocks_of in *. cbn [set_ctx st_bns st_ctx] in *.
  rewrite E1, EQ. rewrite EN in H, Hn. cbn [opt_block] in *. rewrite ?app_nil_r in H, Hn.
  rewrite !map_app in *. cbn [map fst]. rewrite !app_assoc in *. apply nodup_insert; rewrite ?app_nil_r; assumption.
Qed.

(* [comment removed for export] *)
Lemma ids_ok_set_mont : forall s PL EA ri n0, ids_ok s PL EA -> ids_ok (set_mont ri n0 s) PL EA.
Proof. intros s PL EA ri n0 H. exact H. Qed.
Lemma ids_ok_set_recp : forall s PL EA x y, ids_ok s PL EA -> ids_ok (set_recp x y s) PL EA.
Proof. intros s PL EA x y H. exact H. Qed.

(* [comment removed for export] *)
Lemma pl_ids_set : forall PL r p q, In q (pl_ids (pl_set PL r p)) ->
  In q (pl_ids PL) \/ exists a off, p = Some (PHeap a q off).
Proof.
  intros PL r p q H. unfold pl_ids in *. rewrite !in_app_iff in *. cbn [pl_ctx pl_mont pl_set] in H.
  destruct H as [H|H]; [|left; right; exact H].
  apply pl_bn_ids_In in H. destruct H as (k & a & off & Hk & E). destruct (Nat.eq_dec k r) as [->|NE].
  - rewrite pl_set_same in E. right. exists a, off. exact E.
  - rewrite pl_set_other in E by exact NE. left. left. apply pl_bn_ids_In. exists k, a, off. auto.
Qed.

Lemma ids_ok_pl_set_noblock : forall s PL EA r p, ids_ok s PL EA -> match p with Some (PHeap _ _ _) => False | _ => True end ->
  match pl_bn PL r with Some (PHeap _ _ _) => False | _ => True end -> ids_ok s (pl_set PL r p) EA.
Proof.
  intros s PL EA r p H Hp Hold. unfold ids_ok, all_ids in *.
  assert (E : pl_ids (pl_set PL r p) = pl_ids PL).
  { unfold pl_ids. cbn [pl_ctx pl_mont pl_set]. f_equal.
    assert (G : forall n, pl_bn_ids (pl_set PL r p) n = pl_bn_ids PL n).
    { induction n as [|n IH]; cbn [pl_bn_ids]; [reflexivity|]. rewrite IH. f_equal.
      destruct (Nat.eq_dec n r) as [->|NE]; [rewrite pl_set_same| rewrite pl_set_other by exact NE; reflexivity].
      destruct p as [[| | |]|]; destruct (pl_bn PL r) as [[| | |]|]; try reflexivity; contradiction. }
    apply G. }
  rewrite E. exact H.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma own_fp_lib : forall cxo hs s m OW PL EA SPX BX x, lib_state_hc cxo hs s m OW PL EA -> frames_ok PL SPX BX ->
  own_fpc cxo hs s OW PL EA x -> libw x \/ in_block OW x \/ SPX <= x.
Proof.
  intros cxo hs s m OW PL EA SPX BX x HS FROK HO. pose proof (lib_state_h_parts _ _ _ _ _ _ _ HS) as PARTS.
  (* [comment removed for export] *)
  destruct PARTS as (WFS & PWF & IDS & PLB & ERRB).
  destruct HO as [HL|[(r & a & HA & HV & Hn & [Hs|[(p & D & Ed & Hin & Hx)|(y & d & Ep & Hx)]])|[[_ Hc]|[Hmo|He]]]].
  - left. exact HL.
  - pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K.
    destruct K as [q n S Eb Hin Hn'|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
    + right; left. eapply ApBnRepA.in_block_intro; [exact Hin| unfold BN_STRUCT_SZ in *; lia].
    + right; left. eapply ApBnRepA.in_block_intro; [exact Hin| unfold MONT_CTX_SZ in *; lia].
    + right; left. eapply ApBnRepA.in_block_intro; [exact Hin| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; nia].
    + right; right. destruct FROK as (PLF & _). destruct (PLF _ HF) as [X _]. cbn [fst] in X. lia.
    + left. subst. apply libw_const_one. unfold BN_STRUCT_SZ. lia.
  - right; left. eapply ApBnRepA.in_block_intro; [exact Hin| exact Hx].
  - right; right. destruct (pl_of_cases PL r _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [discriminate E'| discriminate E'|].
    destruct FROK as (PLF & _). destruct (PLF (d, d + TMOD_BUF_SZ)) as [X _]; [|cbn [fst] in X; lia].
    apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity].
  - right; left. destruct Hc as [(ac & qc & Ec & Hx)|[(q & H & Hq & Hin & Hx)|(q & Ix & Eq & Hin & Hx)]].
    + destruct PLB as (_ & PC & _). rewrite Ec in PC. eapply ApBnRepA.in_block_intro; [exact PC| exact Hx].
    + eapply ApBnRepA.in_block_intro; [exact Hin| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia].
    + eapply ApBnRepA.in_block_intro; [exact Hin| exact Hx].
  - destruct Hmo as [(am & qm & Em & Hx)|(c & Ec & Hx)].
    + right; left. destruct PLB as (_ & _ & PM). rewrite Em in PM. eapply ApBnRepA.in_block_intro; [exact PM| unfold MONT_CTX_SZ in *; lia].
    + right; right. destruct FROK as (PLF & _). destruct (PLF _ (pl_frames_recp PL c Ec)) as [X _]. cbn [fst] in X. lia.
  - right; left. unfold ApBnRepA.err_fp, in_block in He. destruct He as (b & Hb & Hx). exists b. split; [apply ERRB; apply in_or_app; left; exact Hb| exact Hx].
Qed.

(* [comment removed for export] *)
Lemma own_fp_libA : forall cxo hs s m OW PL EA SPX BX x, lib_state_hc cxo hs s m OW PL EA -> frames_ok PL SPX BX ->
  own_fpA cxo hs s OW PL EA x -> ApBnRepA.libw x \/ in_block OW x \/ SPX <= x < BX.
Proof.
  intros cxo hs s m OW PL EA SPX BX x HS FROK HO. pose proof (lib_state_h_parts _ _ _ _ _ _ _ HS) as PARTS.
  (* [comment removed for export] *)
  destruct PARTS as (WFS & PWF & IDS & PLB & ERRB).
  destruct HO as [HL|[(r & a & HA & HV & Hn & HNO & [Hs|[(p & D & Ed & Hin & Hx)|(y & d & Ep & Hx)]])|[[_ Hc]|[Hmo|He]]]].
  - left. exact HL.
  - pose proof (ref_at_inb _ _ _ _ _ PWF PLB HA) as K.
    destruct K as [q n S Eb Hin Hn'|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
    + right; left. eapply ApBnRepA.in_block_intro; [exact Hin| unfold BN_STRUCT_SZ in *; lia].
    + right; left. eapply ApBnRepA.in_block_intro; [exact Hin| unfold MONT_CTX_SZ in *; lia].
    + right; left. eapply ApBnRepA.in_block_intro; [exact Hin| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; nia].
    + right; right. destruct FROK as (PLF & _). destruct (PLF _ HF) as [X Y]. cbn [fst snd] in X, Y. unfold BN_STRUCT_SZ in Y. lia.
    + exfalso. exact (HNO Er).
  - right; left. eapply ApBnRepA.in_block_intro; [exact Hin| exact Hx].
  - right; right. destruct (pl_of_cases PL r _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [discriminate E'| discriminate E'|].
    destruct FROK as (PLF & _). destruct (PLF (d, d + TMOD_BUF_SZ)) as [X Y]; [|cbn [fst snd] in X, Y; unfold TMOD_BUF_SZ in *; lia].
    apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity].
  - right; left. destruct Hc as [(ac & qc & Ec & Hx)|[(q & H & Hq & Hin & Hx)|(q & Ix & Eq & Hin & Hx)]].
    + destruct PLB as (_ & PC & _). rewrite Ec in PC. eapply ApBnRepA.in_block_intro; [exact PC| exact Hx].
    + eapply ApBnRepA.in_block_intro; [exact Hin| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; lia].
    + eapply ApBnRepA.in_block_intro; [exact Hin| exact Hx].
  - destruct Hmo as [(am & qm & Em & Hx)|(c & Ec & Hx)].
    + right; left. destruct PLB as (_ & _ & PM). rewrite Em in PM. eapply ApBnRepA.in_block_intro; [exact PM| unfold MONT_CTX_SZ in *; lia].
    + right; right. destruct FROK as (PLF & _). destruct (PLF _ (pl_frames_recp PL c Ec)) as [X Y]. cbn [fst snd] in X, Y. unfold RECP_SC_SZ in *. lia.
  - right; left. unfold ApBnRepA.err_fp, in_block in He. destruct He as (b & Hb & Hx). exists b. split; [apply ERRB; apply in_or_app; left; exact Hb| exact Hx].
Qed.

(* [comment removed for export] *)
Theorem lib_state_h_icall : forall s LB cxo hs st m m' OW PL EA SP SPX d n,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> frames_ok PL SPX USTACK_TOP -> SP <= SPX ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (d <= a < d + n)) m m' ->
  w_okc OW LB st PL EA SPX cxo hs (d, d + n) ->
  lib_state_hc cxo hs st m' OW PL EA.
Proof.
  intros s LB cxo hs st m m' OW PL EA SP SPX d n HEAP HS FROK LE AG HW.
  pose proof (lib_state_h_parts _ _ _ _ _ _ _ HS) as PARTS.
  eapply lib_state_hc_agreeA; [exact HS|]. eapply agree_on_mono; [exact AG|]. intros x Hx. split.
  - destruct (own_fp_libA _ _ _ _ _ _ _ _ _ _ HS FROK Hx) as [HL|[(b & Hb & Hr)|Hs]]; [apply libw_clientA; exact HL| | left; lia].
    right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr].
  - assert (FW : Forall (w_okc OW LB st PL EA SPX cxo hs) [(d, d + n)]) by (constructor; [exact HW | constructor]).
    pose proof (own_fp_outside s OW LB m HEAP st PL EA SPX USTACK_TOP PARTS FROK cxo hs [(d, d + n)] x FW (own_fpA_fpc _ _ _ _ _ _ _ Hx)) as O.
    cbn [outside] in O. tauto.
Qed.

Theorem lib_state_h_icall2 : forall s LB cxo hs st m m' OW PL EA SP SPX d1 n1 d2 n2,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> frames_ok PL SPX USTACK_TOP -> SP <= SPX ->
  agree_on (fun a => aclient_addr (OW ++ LB) SP a /\ ~ (d1 <= a < d1 + n1) /\ ~ (d2 <= a < d2 + n2)) m m' ->
  w_okc OW LB st PL EA SPX cxo hs (d1, d1 + n1) -> w_okc OW LB st PL EA SPX cxo hs (d2, d2 + n2) ->
  lib_state_hc cxo hs st m' OW PL EA.
Proof.
  intros s LB cxo hs st m m' OW PL EA SP SPX d1 n1 d2 n2 HEAP HS FROK LE AG HW1 HW2.
  pose proof (lib_state_h_parts _ _ _ _ _ _ _ HS) as PARTS.
  eapply lib_state_hc_agreeA; [exact HS|]. eapply agree_on_mono; [exact AG|]. intros x Hx. split.
  - destruct (own_fp_libA _ _ _ _ _ _ _ _ _ _ HS FROK Hx) as [HL|[(b & Hb & Hr)|Hs]]; [apply libw_clientA; exact HL| | left; lia].
    right; right. exists b. split; [apply in_or_app; left; exact Hb | exact Hr].
  - assert (FW : Forall (w_okc OW LB st PL EA SPX cxo hs) [(d1, d1 + n1); (d2, d2 + n2)]) by (constructor; [exact HW1 | constructor; [exact HW2 | constructor]]).
    pose proof (own_fp_outside s OW LB m HEAP st PL EA SPX USTACK_TOP PARTS FROK cxo hs [(d1, d1 + n1); (d2, d2 + n2)] x FW (own_fpA_fpc _ _ _ _ _ _ _ Hx)) as O.
    cbn [outside] in O. tauto.
Qed.


(* [comment removed for export] *)
Lemma all_ids_owned : forall s m OW PL EA q, lib_state s m OW PL EA -> List.NoDup (map blk_id OW) -> In q (all_ids s PL EA) -> In q (map blk_id OW).
Proof.
  intros s m OW PL EA q HS ND Hq. pose proof (lib_state_h_parts _ _ _ _ _ _ _ HS) as (WFS & PWF & IDS & (PB & PC & PM) & ERRB).
  assert (IB : forall A n, In (q, A, n) OW -> In q (map blk_id OW)) by (intros A n H; apply (in_map blk_id) in H; exact H).
  destruct HS as (_ & _ & _ & (_ & _ & _ & HM)). pose proof HM as (HF & HN & HCX & HMo).
  unfold all_ids in Hq. rewrite !in_app_iff in Hq. destruct Hq as [Hq|[Hq|Hq]].
  - unfold pl_ids in Hq. rewrite !in_app_iff in Hq. destruct Hq as [Hq|[Hq|Hq]].
    + apply pl_bn_ids_In in Hq. destruct Hq as (k & a & off & Hk & Eb).
      pose proof (pl_wf_stored PL k _ PWF Eb) as S. rewrite <- (pl_of_stored PL k S) in Eb.
      destruct (PB k _ Hk Eb) as (n & Hin & _). eapply IB. exact Hin.
    + destruct (pl_ctx PL) as [[ac qc]|]; [|destruct Hq]. destruct Hq as [<-|[]]. eapply IB. exact PC.
    + destruct (pl_mont PL) as [[am qm]|]; [|destruct Hq]. destruct Hq as [<-|[]]. eapply IB. exact PM.
  - unfold ApBnRepA.ea_ids in Hq. apply in_map_iff in Hq. destruct Hq as ([[q0 A0] n0] & E & Hb). cbn in E. subst q0. eapply IB. apply ERRB. exact Hb.
  - (* [comment removed for export] *)
    apply in_map_iff in Hq. destruct Hq as ([q' n] & <- & Hin). cbn [fst].
    unfold blocks_of in Hin. rewrite !in_app_iff in Hin.
    assert (HBN : forall r a, ref_at s OW PL r a -> In (q', n) (bn_blocks (getbn r s)) -> In q' (map blk_id OW)).
    { intros r a HA Hb. destruct (gen_get _ _ _ _ _ _ _ _ HM ND HA) as [[]|(D & _ & HArr)]. unfold bn_blocks, bn_arr in *.
      destruct (bn_d (getbn r s)) as [pp|]; [|contradiction]. destruct Hb as [E|[]]. injection E as <- <-. destruct HArr as [Hi _].
      apply (in_map blk_id) in Hi. exact Hi. }
    destruct Hin as [Hin|[Hin|Hin]].
    + apply in_concat in Hin. destruct Hin as (bl & Hbl & Hq'). apply in_map_iff in Hbl. destruct Hbl as (b & <- & Hb).
      apply In_nth with (d := bn_nil 0) in Hb. destruct Hb as (i & Hi & Eb). fold (getbn i s) in Eb. rewrite <- Eb in Hq'.
      destruct (Nat.ltb_spec i NFIX) as [Hlt|Hge].
      * destruct (pl_of PL i) as [p|] eqn:Ep.
        -- apply (HBN i (place_addr p)); [apply ref_at_fixed; [exact Hlt| exists p; auto]| exact Hq'].
        -- rewrite (HN i Hlt Ep) in Hq'. cbn in Hq'. destruct Hq'.
      * (* [comment removed for export] *)
        destruct (pl_ctx PL) as [[ac qc]|].
        2:{ exfalso. destruct HCX as [Ec Ev]. pose proof (f_equal (@length _) Ev) as L. rewrite length_skipn in L. cbn in L. lia. }
        destruct HCX as (_ & Hs & Ix & LHs & _ & HIT). pose proof (items_gen_length _ _ _ _ _ _ _ _ _ HIT) as [L1 L2]. rewrite length_skipn in L2.
        pose proof (Nat.div_mod_eq (i - NFIX) BN_CTX_POOL_SIZE) as DM.
        assert (Hk : ((i - NFIX) / BN_CTX_POOL_SIZE < length (gx_items (st_ctx s)))%nat) by (unfold BN_CTX_POOL_SIZE in *; lia).
        destruct (nth_error (gx_items (st_ctx s)) ((i - NFIX) / BN_CTX_POOL_SIZE)) as [qi|] eqn:Eq; [|apply nth_error_None in Eq; lia].
        destruct (items_gen_nth _ _ _ _ _ _ _ _ _ _ _ HIT Eq) as (H & HH & HinH & _).
        apply (HBN i (H + 24 * Z.of_nat ((i - NFIX) mod BN_CTX_POOL_SIZE))); [|exact Hq'].
        replace i with (RPool (i - NFIX)) at 1 by (unfold RPool; lia). apply ref_at_pool. exists qi, H. auto.
    + apply in_map_iff in Hin. destruct Hin as (qi & E & Hqi). injection E as <- <-.
      destruct (pl_ctx PL) as [[ac qc]|]; [|destruct HCX as [Ec _]; rewrite Ec in Hqi; destruct Hqi].
      destruct HCX as (_ & Hs & Ix & _ & _ & HIT). destruct (In_nth_error _ _ Hqi) as [k Hk].
      destruct (items_gen_nth _ _ _ _ _ _ _ _ _ _ _ HIT Hk) as (H & _ & HinH & _). eapply IB. exact HinH.
    + destruct (gx_indexes (st_ctx s)) as [qi|] eqn:Eqi; [|destruct Hin]. destruct Hin as [E|[]]. injection E as <- <-.
      destruct (pl_ctx PL) as [[ac qc]|]; [|destruct HCX as [Ec _]; rewrite Ec in Eqi; discriminate Eqi].
      destruct HCX as (_ & Hs & Ix & _ & HCe & _). destruct (HCe eq_refl) as [_ HSt]. unfold stack_rep in HSt. rewrite Eqi in HSt.
      destruct HSt as (HinI & _). eapply IB. exact HinI.
Qed.

(* [comment removed for export] *)
Theorem lib_state_h_heap_pres : forall cxo hs s m m' OW PL EA L SP SPX BX,
  lib_state_hc cxo hs s m OW PL EA -> frames_ok PL SPX BX -> SP <= SPX -> BX <= USTACK_TOP -> agree_on (aclient_addr L SP) m m' -> (forall b, In b OW -> In b L) ->
  lib_state_hc cxo hs s m' OW PL EA.
Proof.
  intros cxo hs s m m' OW PL EA L SP SPX BX HS FROK LE BXT HP HI. eapply lib_state_hc_agreeA; [exact HS|].
  eapply agree_on_mono; [exact HP|]. intros a Ha.
  destruct (own_fp_libA _ _ _ _ _ _ _ _ _ _ HS FROK Ha) as [HL|[(b & Hb & Hr)|Hs]]; [apply libw_clientA; exact HL| | left; lia].
  right; right. exists b. split; [apply HI; exact Hb| exact Hr].
Qed.

(* [comment removed for export] *)
Theorem lib_state_h_free : forall st LB cxo hs s m m' OW PL EA r p D SP SPX BX,
  AHEAP st OW LB m -> lib_state_hc cxo hs s m OW PL EA -> frames_ok PL SPX BX -> SP <= SPX -> BX <= USTACK_TOP ->
  In r hs -> vref r s -> bn_d (getbn r s) = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax (getbn r s))) OW ->
  agree_on (aclient_addr (lb_remove p (OW ++ LB)) SP) m m' ->
  lib_state_hc cxo hs s m' (lb_remove p OW) PL EA.
Proof.
  intros st LB cxo hs s m m' OW PL EA r p D SP SPX BX HEAP HS FROK LE BXT Hr HV Ed Hin HP.
  pose proof (lib_state_h_parts _ _ _ _ _ _ _ HS) as PARTS. pose proof PARTS as (WFS & PWF & IDS & PLB & ERRB).
  pose proof (AH_nodup_l _ _ _ _ HEAP) as ND.
  assert (HS' : lib_state_hc cxo hs s m' OW PL EA).
  { eapply lib_state_hc_agreeA; [exact HS|]. eapply agree_on_mono; [exact HP|]. intros a Ha.
    destruct (own_fp_blockA OW s PL EA PARTS cxo hs a Ha) as [HL|[(q & A & n & Hq & Hx & _)|(iv & Hiv & Hxi)]]; [apply libw_clientA; exact HL| |].
    - right; right. exists (q, A, n). split; [|exact Hx]. apply lb_remove_In. split; [apply in_or_app; left; exact Hq|].
      cbn [blk_id fst]. intros ->. destruct (AH_addr_unique OW p A n D _ ND Hq Hin) as [-> ->].
      eapply (own_fp_not_limbs st OW LB m HEAP s PL EA SPX BX PARTS FROK cxo hs a r p D); eauto using own_fpA_fpc.
    - left. destruct FROK as (PLF & _). destruct (PLF iv Hiv). lia. }
  (* [comment removed for export] *)
  pose proof HS' as (HC & (HE1 & HE2) & HO & (S1 & S2 & S3 & HM)).
  pose proof (bn_in_m r s p HV Ed) as Hpm. pose proof (ids_m_nodup _ _ _ IDS) as NDm.
  assert (KEEP : forall q A n, q <> p -> In (q, A, n) OW -> In (q, A, n) (lb_remove p OW)) by (intros q A n NE H; apply lb_remove_In; split; [exact H| exact NE]).
  assert (KPL : forall q A n, In q (pl_ids PL) -> In (q, A, n) OW -> In (q, A, n) (lb_remove p OW)).
  { intros q A n Hq H. apply KEEP; [|exact H]. intros ->. eapply (ids_pl_m s PL EA p p IDS); eauto. }
  split; [exact HC|]. split.
  { split; [exact HE1|]. eapply ApBnRepA.err_mem_agree; [apply agree_on_refl| intros a Ha; exact I| intros x Hx; exact I| | exact HE2].
    intros q A n Hq. apply KEEP. intros ->. eapply (ids_ea_m _ _ _ p p IDS); eauto. }
  split; [exact HO|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply (gen_transport (fun _ => True)); [exact HM| apply agree_on_refl| auto| | | | | | auto|].
  - intros ac qc Ec H. apply KPL; [eapply in_pl_ids_ctx; exact Ec| exact H].
  - intros q H Hq HinH. apply KEEP; [|exact HinH]. intros ->. eapply (ids_bn_item_neq r s p p); eauto.
  - intros q Ix Eq HinI. apply KEEP; [|exact HinI]. intros ->. eapply (ids_bn_idx_neq r s p p); eauto.
  - intros am qm Em H. apply KPL; [eapply in_pl_ids_mont; exact Em| exact H].
  - intros r' p' Hr' E OK. destruct p' as [a q off|a|a d|a]; try exact OK. destruct OK as (n & Hin' & H1 & H2). exists n. split; [|lia].
    destruct (pl_of_cases PL r' _ E) as [[_ E']|[(am & qm & M & Em & E' & _)|[S Eb]]]; [discriminate E'| |].
    + injection E' as Ea Eq Eo. subst q. apply KPL; [eapply in_pl_ids_mont; exact Em| exact Hin'].
    + apply KPL; [eapply in_pl_ids_bn; [exact Hr'| exact Eb]| exact Hin'].
  - intros r' a' HA' [Hh|HR]; [left; exact Hh|]. destruct (in_dec Nat.eq_dec r' hs) as [Hi|Hni]; [left; exact Hi|]. right.
    eapply (bn_rep_transport (fun _ => True)); [apply agree_on_refl| auto| | exact HR].
    intros p' D' Ed' Hin'. apply KEEP; [|exact Hin']. intros ->. assert (NE : r <> r') by (intros ->; contradiction).
    eapply (ids_bn_neq r r' s p p); eauto. eapply gen_ref_valid; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma st_wf_init : st_wf (st_init : ST).
Proof.
  unfold st_wf, st_init, ctx_wf. cbn. split; [reflexivity|]. split.
  - intros r Hr Hn. unfold getbn. cbn [st_bns].
    do 11 (destruct r as [|r]; [apply bg_ok_nil; left; reflexivity|]). destruct r as [|r]; [exfalso; apply Hn; reflexivity|]. cbn in Hr. lia.
  - split; [reflexivity|]. repeat split; try reflexivity; try lia. left. auto.
Qed.

Lemma pl_wf_empty : pl_wf pl_empty.
Proof. split; [intros r p E; discriminate E|]. split; [intros r r' p p' iv iv' _ E; discriminate E| exact I]. Qed.

Theorem lib_state_init : forall m OW, lib_inv_bgr m OW -> exists EA, lib_state st_init m OW pl_empty EA /\ List.NoDup (ApBnRepA.ea_ids EA).
Proof.
  intros m OW ((EA & ND & HC & HE & HO) & HONE). pose proof I as HGOT. exists EA. split; [|exact ND].
  split; [exact HC|]. split; [exact HE|]. split; [split; [exact HO| exact HGOT]|]. split; [exact st_wf_init|]. split; [exact pl_wf_empty|].
  split. { unfold ids_ok, all_ids, blocks_of. cbn. rewrite ?app_nil_r. exact ND. }
  split.
  { intros r p Hr E. destruct (pl_of_cases pl_empty r p E) as [[-> ->]|[(am & qm & _ & Em & _)|[S Eb]]]; [|discriminate Em| discriminate Eb].
    split; [exact I|]. right. exists DATA_ONE. split; [split; reflexivity|]. cbn. auto. }
  split.
  { intros r Hr E. unfold getbn, st_init. cbn [st_bns]. do 11 (destruct r as [|r]; [reflexivity|]). destruct r as [|r]; [discriminate E|]. unfold NFIX in Hr. lia. }
  split; [cbn; auto| split; exact I].
Qed.

Theorem lib_state_fini : forall m OW EA, lib_state st_init m OW pl_empty EA -> List.NoDup (ApBnRepA.ea_ids EA) -> lib_inv_bgr m OW.
Proof.
  intros m OW EA (HC & HE & (HO & HGOT) & (_ & _ & _ & (HF & _))) ND. split; [exists EA; auto| exact I].
Qed.

(* [comment removed for export] *)
Lemma got_add_sub : forall cxo hs (s : ST) m OW PL EA, lib_state_hc cxo hs s m OW PL EA -> got_arith_cells m ->     (* [comment removed for export] *)
  ro_cells ctasegs m GOT_BN_ADD [C8 (wz 0x235c38)] /\ ro_cells ctasegs m GOT_BN_SUB [C8 (wz 0x23633c)].
Proof.
  intros cxo hs s m OW PL EA _ HG. exact HG.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ref_at_range : forall st OW PL EA SPX BX s LB m r a,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  0 < a /\ (a + 24 <= ACEIL \/ (SPX <= a /\ a + 24 < 2^63)) /\ (a + 24 <= 0x10000 \/ 0xbcb000 <= a).
Proof.
  intros st OW PL EA SPX BX s LB m r a HEAP PARTS FROK HA NE. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
  pose proof (skind_range s OW LB m HEAP st PL EA SPX BX PARTS FROK r a (ref_at_inb _ _ _ _ _ (proj1 (proj2 PARTS)) (proj1 (proj2 (proj2 (proj2 PARTS)))) HA))
    as [(C1 & I1 & P1)|[[C1 U1]|[-> ->]]]; [| | exfalso; exact (NE eq_refl)].
  - split; [exact P1|]. split; [left; exact C1| exact I1].
  - destruct FROK as (PLF & CSP & _).
    pose proof (ref_at_inb _ _ _ _ _ (proj1 (proj2 PARTS)) (proj1 (proj2 (proj2 (proj2 PARTS)))) HA) as K.
    destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea];
      [exfalso; pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin); unfold ablock_range, BN_STRUCT_SZ in *; lia
      | exfalso; pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin); unfold ablock_range, MONT_CTX_SZ in *; lia
      | exfalso; pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin); unfold ablock_range, ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; nia
      | | exfalso; exact (NE Er)].
    destruct (PLF _ HF) as [X _]. cbn [fst] in X. split; [lia|]. split; [right; lia| right; lia].
Qed.

Lemma ref_at_client : forall st OW PL EA SPX BX s LB m r a L SP x,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  SP <= SPX -> BX <= USTACK_TOP -> (forall b, In b OW -> In b L) -> a <= x < a + 24 -> aclient_addr L SP x.
Proof.
  intros st OW PL EA SPX BX s LB m r a L SP x HEAP PARTS FROK HA NE LE BXT HI Hx.
  pose proof (ref_at_inb _ _ _ _ _ (proj1 (proj2 PARTS)) (proj1 (proj2 (proj2 (proj2 PARTS)))) HA) as K.
  destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
  - right; right. exists (q, a, n). split; [apply HI; exact Hin|]. cbn. unfold BN_STRUCT_SZ in *. lia.
  - right; right. exists (qm, am, MONT_CTX_SZ). split; [apply HI; exact Hin|]. cbn. unfold MONT_CTX_SZ in *. lia.
  - right; right. exists (q, H, ITEM_SZ). split; [apply HI; exact Hin|]. cbn. unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *. nia.
  - left. destruct FROK as (PLF & _). destruct (PLF _ HF) as [X Y]. cbn [fst snd] in X, Y. unfold BN_STRUCT_SZ in Y. lia.
  - exfalso. exact (NE Er).
Qed.

(* [comment removed for export] *)
Lemma ref_at_lb_remove : forall st OW PL EA r' p r a,
  lib_parts st OW PL EA -> vref r' st -> bn_d (getbn r' st) = Some p -> ref_at st OW PL r a -> ref_at st (lb_remove p OW) PL r a.
Proof.
  intros st OW PL EA r' p r a (WFS & PWF & IDS & PLB & ERRB) HV Ed HA. unfold ref_at in *. destruct (r <? NFIX)%nat; [exact HA|].
  destruct HA as (q & H & Eq & Hin & Ea). exists q, H. split; [exact Eq|]. split; [|exact Ea].
  apply lb_remove_In. split; [exact Hin|]. cbn [blk_id fst]. intros ->. eapply (ids_bn_item_neq r' st p p); eauto using ids_m_nodup. eapply nth_error_In. exact Eq.
Qed.


(* [comment removed for export] *)
Lemma bn_arr_rclient : forall st OW PL EA SPX BX s LB m r D L SP x,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> vref r st -> r <> ROne ->
  bn_arr m OW (pl_of PL r) D (getbn r st) -> SP <= SPX -> BX <= USTACK_TOP -> (forall b, In b OW -> In b L) ->
  D <= x < D + 8 * Z.of_nat (bn_dmax (getbn r st)) -> aclient_addr L SP x.
Proof.
  intros st OW PL EA SPX BX s LB m r D L SP x HEAP PARTS FROK HV NE ARR LE BXT HI Hx.
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r D HV NE ARR) as (_ & _ & _ & DC & _ & _).
  unfold bn_arr in ARR. destruct (bn_d (getbn r st)) as [p|] eqn:Ed.
  - destruct ARR as [Hin _]. right; right. exists (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))). split; [apply HI; exact Hin|]. cbn. lia.
  - destruct (pl_of PL r) as [[a q off|a|a d|a]|] eqn:Ep;
      try (destruct ARR as [-> Eb]; unfold bn_dmax in Hx; rewrite Eb in Hx; cbn in Hx; lia).
    + (* [comment removed for export] *)
      destruct ARR as (-> & _ & HL).
      destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exfalso; exact (NE eq_refl)| discriminate E'|].
      destruct FROK as (PLF & _). destruct (PLF (d, d + TMOD_BUF_SZ)) as [X Y].
      { apply pl_frames_In. left. exists r. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
      cbn [fst snd] in X, Y. left. unfold bn_dmax in Hx. rewrite HL in Hx. unfold TMOD_BUF_SZ in Y. lia.
    + exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
      exact (proj2 (proj2 (proj2 (proj1 (proj1 (proj2 PARTS)) r _ Eb)))).
Qed.

Lemma bn_arr_heap_pres : forall st OW PL EA SPX BX s LB m m' r D L SP,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> vref r st -> r <> ROne ->
  bn_arr m OW (pl_of PL r) D (getbn r st) -> SP <= SPX -> BX <= USTACK_TOP -> (forall b, In b OW -> In b L) -> agree_on (aclient_addr L SP) m m' ->
  bn_arr m' OW (pl_of PL r) D (getbn r st).
Proof.
  intros st OW PL EA SPX BX s LB m m' r D L SP HEAP PARTS FROK HV NE ARR LE BXT HI HP.
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r D HV NE ARR) as (U & _).
  eapply bn_arr_of_u64arr; [exact ARR|]. eapply LibKitA.u64arr_agree; [exact HP| exact U|].
  intros x Hx. rewrite wlimbs_length in Hx. eapply bn_arr_rclient; eauto; unfold bn_dmax; lia.
Qed.


(* [comment removed for export] *)
Definition wref (PL : placement) (r : bnref) : Prop := r <> ROne /\ forall a d, pl_of PL r <> Some (PFrameBuf a d).

Lemma wref_pool : forall PL i, wref PL (RPool i).
Proof. intros PL i. split; [unfold RPool, ROne, NFIX; lia|]. intros a d. rewrite pl_of_pool. discriminate. Qed.

Lemma wref_heap : forall PL r a q off, pl_of PL r = Some (PHeap a q off) -> wref PL r.
Proof. intros PL r a q off E. split; [intros ->; rewrite pl_of_one in E; discriminate E|]. intros a' d. rewrite E. discriminate. Qed.

Lemma wref_frame : forall PL r a, pl_of PL r = Some (PFrame a) -> wref PL r.
Proof. intros PL r a E. split; [intros ->; rewrite pl_of_one in E; discriminate E|]. intros a' d. rewrite E. discriminate. Qed.

Lemma wref_pl_other : forall PL r r' p, r' <> r -> wref PL r' -> wref (pl_set PL r p) r'.
Proof. intros PL r r' p NE [H1 H2]. split; [exact H1|]. intros a d. rewrite pl_of_set_other by exact NE. apply H2. Qed.

(* [comment removed for export] *)
Lemma bn_arr_null : forall PL r m OW D b, pl_wf PL -> wref PL r -> bn_d b = None -> bn_arr m OW (pl_of PL r) D b -> D = 0 /\ bn_buf b = [].
Proof.
  intros PL r m OW D b WF [NE NF] Ed ARR. unfold bn_arr in ARR. rewrite Ed in ARR.
  destruct (pl_of PL r) as [[a q off|a|a d|a]|] eqn:Ep; try exact ARR.
  - exfalso. exact (NF a d eq_refl).
  - exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exact (NE eq_refl)| discriminate E'|].
    exact (proj2 (proj2 (proj2 (proj1 WF r _ Eb)))).
Qed.


(* [comment removed for export] *)
Lemma bn_arr_nil_intro : forall PL r m OW D b, pl_wf PL -> wref PL r -> D = 0 -> bn_buf b = [] -> bn_d b = None -> bn_arr m OW (pl_of PL r) D b.
Proof.
  intros PL r m OW D b WF [NE NF] -> Eb Ed. unfold bn_arr. rewrite Ed.
  destruct (pl_of PL r) as [[a q off|a|a d|a]|] eqn:Ep; try (split; [reflexivity| exact Eb]).
  - exfalso. exact (NF a d eq_refl).
  - exfalso. destruct (pl_of_cases PL r _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb']]]; [exact (NE eq_refl)| discriminate E'|].
    exact (proj2 (proj2 (proj2 (proj1 WF r _ Eb')))).
Qed.

(* [comment removed for export] *)
Lemma arr_arr_disj : forall st OW PL EA SPX BX s LB m r r' p D D',
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> r <> r' -> vref r st -> vref r' st -> r' <> ROne ->
  bn_d (getbn r st) = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) OW -> bn_arr m OW (pl_of PL r') D' (getbn r' st) ->
  D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= D' \/ D' + 8 * Z.of_nat (bn_dmax (getbn r' st)) <= D.
Proof.
  intros st OW PL EA SPX BX s LB m r r' p D D' HEAP PARTS FROK NE HV HV' NRO Ed Hin ARR.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI).
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r' D' HV' NRO ARR) as (_ & _ & D0 & DC & _ & _).
  pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d (getbn r' st)) as [p'|] eqn:Ed'.
  - destruct ARR' as [Hin' _]. exact (limbs_limbs_disj s OW LB m HEAP st PL EA PARTS r r' p D _ p' D' _ NE HV HV' Ed Ed' Hin Hin').
  - destruct (pl_of PL r') as [[a q off|a|a d|a]|] eqn:Ep; try (destruct ARR' as [E0 E]; unfold bn_dmax at 2; rewrite E; cbn; subst D'; unfold DATA_ONE; lia).
    + (* [comment removed for export] *)
      destruct ARR' as (-> & _ & HL).
      destruct (pl_of_cases PL r' _ Ep) as [[-> _]|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [exfalso; exact (NRO eq_refl)| discriminate E'|].
      destruct FROK as (PLF & CSP & _). destruct (PLF (d, d + TMOD_BUF_SZ)) as [X _].
      { apply pl_frames_In. left. exists r'. rewrite Eb. split; [exact (proj1 S)| right; left; reflexivity]. }
      cbn [fst] in X. left. lia.
Qed.

(* [comment removed for export] *)
Lemma ref_at_fresh_sep : forall st OW PL EA SPX BX s LB m r a pn An n,
  AHEAP s ((pn, An, n) :: OW) LB m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> ref_at st OW PL r a -> r <> ROne ->
  An + n <= a \/ a + 24 <= An.
Proof.
  intros st OW PL EA SPX BX s LB m r a pn An n HEAP PARTS FROK HA NE.
  pose proof (AH_nodup _ _ _ _ HEAP) as ND. cbn [map blk_id fst app] in ND. apply NoDup_cons_iff in ND. destruct ND as [Hpn _].
  pose proof (AH_range_gen _ _ _ _ _ HEAP ltac:(left; reflexivity)) as (_ & _ & _ & BC & _). cbn [blk_addr blk_size fst snd] in BC.
  assert (BLK : forall q A nq, In (q, A, nq) OW -> A <= a -> a + 24 <= A + nq -> An + n <= a \/ a + 24 <= An).
  { intros q A nq Hin H1 H2.
    assert (NEq : pn <> q) by (intros ->; apply Hpn; rewrite map_app; apply in_or_app; left; apply (in_map blk_id) in Hin; exact Hin).
    pose proof (AH_disjoint_gen _ _ _ _ (pn, An, n) (q, A, nq) HEAP ltac:(left; reflexivity) ltac:(right; apply in_or_app; left; exact Hin) NEq) as DJ.
    cbn [blk_addr blk_size fst snd] in DJ. lia. }
  pose proof (ref_at_inb _ _ _ _ _ (proj1 (proj2 PARTS)) (proj1 (proj2 (proj2 (proj2 PARTS)))) HA) as K.
  destruct K as [q nq S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
  - eapply BLK; [exact Hin| lia| unfold BN_STRUCT_SZ in *; lia].
  - eapply BLK; [exact Hin| lia| unfold MONT_CTX_SZ in *; lia].
  - eapply BLK; [exact Hin| lia| unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *; nia].
  - left. destruct FROK as (PLF & CSP & _). destruct (PLF _ HF) as [X _]. cbn [fst] in X. lia.
  - exfalso. exact (NE Er).
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma items_gen_app1 : forall (R : bnR) m OW items Hs vals k0 prev p Hn new16,
  items_gen R true m OW items Hs vals k0 prev -> In (p, Hn, ITEM_SZ) OW ->
  length new16 = BN_CTX_POOL_SIZE -> bns_gen R Hn new16 (BN_CTX_POOL_SIZE * (k0 + length items)) ->
  items_gen R true m OW (items ++ [p]) (Hs ++ [Hn]) (vals ++ new16) k0 prev.
Proof.
  intros R m OW items. induction items as [|q items IH]; intros Hs vals k0 prev p Hn new16 HG Hin L16 HB;
    destruct Hs as [|H0 Hs]; cbn [items_gen app] in HG |- *; try contradiction.
  - subst vals. cbn [app length]. rewrite Nat.add_0_r in HB. split; [exact Hin|]. split; [rewrite L16; lia|].
    rewrite firstn_all2 by (rewrite L16; lia). split; [exact HB|]. split; [intros E; discriminate E|].
    rewrite skipn_all2 by (rewrite L16; lia). reflexivity.
  - destruct HG as (Hin0 & H16 & Hb & HL & HG). split; [exact Hin0|]. split; [rewrite length_app; lia|].
    rewrite firstn_app, (proj2 (Nat.sub_0_le _ _)) by lia. cbn [firstn]. rewrite app_nil_r. split; [exact Hb|]. split; [intros E; discriminate E|].
    rewrite skipn_app, (proj2 (Nat.sub_0_le _ _)) by lia. cbn [skipn].
    apply IH; [exact HG| exact Hin| exact L16|]. cbn [length] in HB. replace (k0 + S (length items))%nat with (S k0 + length items)%nat in HB by lia. exact HB.
Qed.

(* [comment removed for export] *)
Lemma bns_gen_zeros : forall (R : bnR) (n : nat) m A i,
  (forall a j, (i <= j)%nat -> rw_cells ctasegs m a (bn_cells 0 (bn_nil 0)) -> R a (bn_nil 0) (RPool j)) ->
  rw_cells ctasegs m A [CB (24 * n) (repeat (Z_to_bv 8 0) (24 * n))] -> bns_gen R A (repeat (bn_nil 0) n) i.
Proof.
  intros R n. induction n as [|n IH]; intros m A i HR HZ; cbn [repeat bns_gen]; [exact I|].
  assert (SPLIT : rw_cells ctasegs m A (bn_cells 0 (bn_nil 0) ++ [CB (24 * n) (repeat (Z_to_bv 8 0) (24 * n))])).
  { eapply LibKitA.rw_cells_recast; [exact HZ| | |].
    - cbn [bn_cells app cells_wf cell_wf]. rewrite repeat_length. tauto.
    - cbn [bn_cells cells_bytes cbytes app]. rewrite !app_nil_r.
      replace (24 * S n)%nat with (24 + 24 * n)%nat by lia. rewrite repeat_app. reflexivity.
    - cbn [bn_cells cells_size csize app]. lia. }
  apply BnKit2.bk_rw_cells_app in SPLIT. destruct SPLIT as [B1 B2]. cbn [bn_cells cells_size csize Nat.add] in B2. change (Z.of_nat 24) with 24 in B2.
  split; [apply HR; [lia| exact B1]|]. eapply IH; [| exact B2]. intros a j Hj HC. apply HR; [lia| exact HC].
Qed.

(* [comment removed for export] *)
Lemma ids_ok_new_item : forall s s' PL EA p,
  ids_ok s PL EA -> ~ In p (all_ids s PL EA) ->
  st_bns s' = st_bns s ++ repeat (bn_nil 0) BN_CTX_POOL_SIZE ->
  gx_items (st_ctx s') = gx_items (st_ctx s) ++ [p] -> gx_indexes (st_ctx s') = gx_indexes (st_ctx s) ->
  ids_ok s' PL EA.
Proof.
  intros s s' PL EA p H Hn EB EI EX. unfold ids_ok, all_ids in *.
  rewrite app_assoc in H, Hn |- *. set (PIDS := pl_ids PL ++ ApBnRepA.ea_ids EA) in *. clearbody PIDS.
  unfold blocks_of in *. rewrite EB, EI, EX.
  rewrite (map_app bn_blocks), concat_app, BgSpecs.concat_blocks_repeat_nil, app_nil_r, (map_app (fun p0 : bptr => (p0, POOL_ITEM_BYTES))). cbn [map].
  rewrite !map_app in *. cbn [map fst app] in *. rewrite <- !app_assoc in *. cbn [app] in *.
  set (A := map fst (concat (map bn_blocks (st_bns s)))) in *. set (B := map fst (map (fun p0 : bptr => (p0, POOL_ITEM_BYTES)) (gx_items (st_ctx s)))) in *.
  set (C := map fst (opt_block (gx_indexes (st_ctx s)) (4 * Z.of_nat BN_CTX_START_FRAMES))) in *.
  assert (E1 : forall X, PIDS ++ A ++ B ++ X = (PIDS ++ A ++ B) ++ X) by (intros; rewrite <- !app_assoc; reflexivity).
  rewrite E1 in H, Hn. rewrite E1. apply nodup_insert; assumption.
Qed.

Lemma nth_app_l : forall {A} (l l' : list A) i d, (i < length l)%nat -> nth i (l ++ l') d = nth i l d.
Proof. intros. apply app_nth1. assumption. Qed.

(* [comment removed for export] *)
Theorem lib_state_cx_close_newitem : forall hs s s' m OW PL EA Hs Ia p Hn ac qc,
  lib_state_hc true hs s m OW PL EA -> List.NoDup (map blk_id OW) -> pl_ctx PL = Some (ac, qc) ->
  st_bns s' = st_bns s ++ repeat (bn_nil 0) BN_CTX_POOL_SIZE ->
  gx_items (st_ctx s') = gx_items (st_ctx s) ++ [p] -> gx_indexes (st_ctx s') = gx_indexes (st_ctx s) -> mont_cells s' = mont_cells s ->
  recp_cells s' = recp_cells s -> st_wf s' -> ~ In p (all_ids s PL EA) -> In (p, Hn, ITEM_SZ) OW ->
  rw_cells ctasegs m Hn [CB (24 * BN_CTX_POOL_SIZE) (repeat (Z_to_bv 8 0) (24 * BN_CTX_POOL_SIZE))] ->
  cx_view m OW PL s' (Hs ++ [Hn]) Ia ->
  lib_state_hc false hs s' m OW PL EA.
Proof.
  intros hs s s' m OW PL EA Hs Ia p Hn ac qc HS ND EC EB EI EX EMC ERC WF' FRESH HinN HZ CV.
  pose proof HS as (HC & HE & HO & (S1 & S2 & S3 & (HF & HN & HCX & HM))).
  pose proof (proj1 S1) as EL.
  assert (EG : forall r, (r < length (st_bns s))%nat -> getbn r s' = getbn r s) by (intros r Hr; unfold getbn; rewrite EB; apply nth_app_l; exact Hr).
  split; [exact HC|]. split; [exact HE|]. split; [exact HO|]. split; [exact WF'|]. split; [exact S2|].
  split; [eapply ids_ok_new_item; eauto|].
  split. { intros r pp Hr E. destruct (HF r pp Hr E) as [OK H]. split; [exact OK|]. rewrite EG by (rewrite EL; lia). exact H. }
  split. { intros r Hr E. rewrite EG by (rewrite EL; lia). apply HN; assumption. }
  split.
  - unfold cx_view in CV. rewrite EC in CV |- *. rewrite EC in HCX. destruct HCX as (Hinc & Hs0 & I0 & LHs0 & _ & HIT).
    destruct CV as (Hinc' & LHs & HCe & HSt & HItems & HLinks).
    assert (LH : length Hs = length (gx_items (st_ctx s))).
    { rewrite EI, length_app, length_app in LHs. cbn [length] in LHs. lia. }
    assert (Hs0 = Hs) as ->.
    { eapply items_gen_Hs_of_blocks; [exact HIT| exact ND| exact LH|].
      intros k q Hk. specialize (HItems k q). rewrite EI in HItems. rewrite nth_error_app1 in HItems by (apply nth_error_Some; congruence).
      specialize (HItems Hk). rewrite nth_app_l in HItems; [exact HItems|]. rewrite LH. apply nth_error_Some. congruence. }
    split; [exact Hinc|]. exists (Hs ++ [Hn]), Ia. split; [exact LHs|]. split; [intros _; split; assumption|].
    rewrite EB, EI, skipn_app, (proj2 (Nat.sub_0_le _ _)) by (rewrite EL; lia). cbn [skipn].
    eapply items_gen_close; [| exact HLinks].
    pose proof (items_gen_length _ _ _ _ _ _ _ _ _ HIT) as [L1 L2].
    apply items_gen_app1; [| exact HinN| apply repeat_length|].
    + (* [comment removed for export] *)
      eapply items_gen_impl; [|exact HIT]. intros a b i H. exact H.
    + rewrite Nat.add_0_l. eapply (bns_gen_zeros _ BN_CTX_POOL_SIZE m); [| exact HZ].
      intros a j Hj HCj. right. exists 0. split; [rewrite pl_of_pool; exact HCj|]. rewrite pl_of_pool. cbn. auto.
  - rewrite EMC, ERC. exact HM.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition recp_at (PL : placement) (an : Z) : Prop :=
  pl_bn PL RRecpN = Some (PFrame an) /\ pl_bn PL RRecpNr = Some (PFrame (an + 24)) /\ pl_recp PL = Some (an + 48).

Lemma stored_RRecpN : stored_ref RRecpN.   Proof. unfold stored_ref, RRecpN, ROne, NFIX. cbn. repeat split; try lia; reflexivity. Qed.
Lemma stored_RRecpNr : stored_ref RRecpNr. Proof. unfold stored_ref, RRecpNr, ROne, NFIX. cbn. repeat split; try lia; reflexivity. Qed.

Lemma recp_at_refN : forall st OW PL an, recp_at PL an -> ref_at st OW PL RRecpN an.
Proof.
  intros st OW PL an (E & _ & _). apply ref_at_fixed; [exact (proj1 stored_RRecpN)|].
  exists (PFrame an). rewrite (pl_of_stored PL RRecpN stored_RRecpN), E. auto.
Qed.
Lemma recp_at_refNr : forall st OW PL an, recp_at PL an -> ref_at st OW PL RRecpNr (an + 24).
Proof.
  intros st OW PL an (_ & E & _). apply ref_at_fixed; [exact (proj1 stored_RRecpNr)|].
  exists (PFrame (an + 24)). rewrite (pl_of_stored PL RRecpNr stored_RRecpNr), E. auto.
Qed.
Lemma recp_at_wrefN : forall PL an, recp_at PL an -> wref PL RRecpN.
Proof. intros PL an (E & _ & _). eapply wref_frame. rewrite (pl_of_stored PL RRecpN stored_RRecpN). exact E. Qed.
Lemma recp_at_wrefNr : forall PL an, recp_at PL an -> wref PL RRecpNr.
Proof. intros PL an (_ & E & _). eapply wref_frame. rewrite (pl_of_stored PL RRecpNr stored_RRecpNr). exact E. Qed.
Lemma recp_at_recp : forall PL an, recp_at PL an -> pl_recp PL = Some (an + 48).
Proof. intros PL an (_ & _ & E). exact E. Qed.

(* [comment removed for export] *)
Lemma lib_state_recp_cells : forall cxo hs st m OW PL EA c,
  lib_state_hc cxo hs st m OW PL EA -> pl_recp PL = Some c -> rw_cells ctasegs m c (recp_cells st).
Proof. intros cxo hs st m OW PL EA c (_ & _ & _ & (_ & _ & _ & (_ & _ & _ & [_ HRc]))) Ec. rewrite Ec in HRc. exact HRc. Qed.

Lemma lib_state_mont_cells : forall cxo hs st m OW PL EA am qm,
  lib_state_hc cxo hs st m OW PL EA -> pl_mont PL = Some (am, qm) -> rw_cells ctasegs m (am + 72) (mont_cells st).
Proof. intros cxo hs st m OW PL EA am qm (_ & _ & _ & (_ & _ & _ & (_ & _ & _ & [HMo _]))) Em. rewrite Em in HMo. exact (proj2 HMo). Qed.

(* [comment removed for export] *)
Lemma recp_facts : forall st OW PL EA SPX BX s LB m c,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> pl_recp PL = Some c ->
  0 < c /\ SPX <= c /\ c + RECP_SC_SZ <= BX /\ BX < 2^63
  /\ (forall r a, ref_at st OW PL r a -> a + 24 <= c \/ c + RECP_SC_SZ <= a)
  /\ (forall r p D, vref r st -> bn_d (getbn r st) = Some p -> In (p, D, 8 * Z.of_nat (bn_dmax (getbn r st))) OW ->
        D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= c).
Proof.
  intros st OW PL EA SPX BX s LB m c HEAP PARTS FROK Ec. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
  destruct (recp_frame OW st PL EA SPX BX PARTS FROK c Ec) as (Cc & Sc & Uc & Pc).
  pose proof FROK as (PLF & CSP & BXB). destruct (PLF _ (pl_frames_recp PL c Ec)) as [_ X]. cbn [snd] in X.
  split; [exact Pc|]. split; [exact Sc|]. split; [exact X|]. split; [exact BXB|]. split.
  - intros r a HA. unfold RECP_SC_SZ in *.
    destruct (Z.le_gt_cases (a + 24) c); [left; lia|]. destruct (Z.le_gt_cases (c + 12) a); [right; lia|]. exfalso.
    eapply (struct_not_mont s OW LB m HEAP st PL EA SPX BX PARTS FROK r a (Z.max a c)); [exact HA| lia|].
    right. exists c. split; [exact Ec| unfold RECP_SC_SZ; lia].
  - intros r p D HV Ed Hin. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & BC & _). lia.
Qed.

Lemma libw_below_ceiling : forall s OW LB m a, AHEAP s OW LB m -> libw a -> a < ACEIL.   (* [comment removed for export] *)
Proof.
  intros s OW LB m a HEAP HL. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR. revert HL.
  unfold libw, LIBW_bgr, ARun.LIBW_A, CONST_ONE, BN_STRUCT_SZ. cbn [rin_ivs app fst snd]. lia.
Qed.

Lemma mont_cells_set_recp : forall x y (s : ST), mont_cells (set_recp x y s) = mont_cells s.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Theorem lib_state_set_recp : forall s LB SPX BX cxo hs st m m' OW PL EA c bits sh,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> frames_ok PL SPX BX -> pl_recp PL = Some c ->
  munch [(c, c + RECP_SC_SZ)] m m' -> wmono ctasegs m m' ->
  rw_cells ctasegs m' c (recp_cells (set_recp bits sh st)) ->
  lib_state_hc cxo hs (set_recp bits sh st) m' OW PL EA.
Proof.
  intros s LB SPX BX cxo hs st m m' OW PL EA c bits sh HEAP HS FROK Ec MU WM HRC.
  pose proof (lib_state_h_parts _ _ _ _ _ _ _ HS) as PARTS. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
  pose proof HS as (HC & (HE1 & HE2) & HO & (S1 & S2 & S3 & HM)).
  destruct (recp_frame OW st PL EA SPX BX PARTS FROK c Ec) as (Cc & Sc & Uc & Pc).
  set (P := fun x => x < c \/ c + RECP_SC_SZ <= x).
  assert (AG : agree_on P m m').
  { eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]. intros x Hx. cbn [outside fst snd]. subst P. cbn beta in Hx. split; [lia| exact I]. }
  assert (HL : forall a, ApBnRepA.libw a -> P a) by (intros a Ha; left; pose proof (libw_below_ceiling _ _ _ _ a HEAP (libw_bn a Ha)); lia).
  assert (HL' : forall a, libw a -> P a) by (intros a Ha; left; pose proof (libw_below_ceiling _ _ _ _ a HEAP Ha); lia).
  assert (NM : forall x, (mont_fp PL x -> False) -> P x).
  { intros x Hx. subst P. cbn beta. destruct (Z.lt_ge_cases x c); [left; lia|]. destruct (Z.le_gt_cases (c + RECP_SC_SZ) x); [right; lia|].
    exfalso. apply Hx. right. exists c. split; [exact Ec| lia]. }
  split; [eapply ApBnRepA.crypto_statics_agree; eauto|].
  split. { split; [eapply ApBnRepA.err_statics_agree; eauto|]. eapply ApBnRepA.err_mem_agree; [exact AG| exact HL| | | exact HE2]; [|auto].
           intros x Hx. left. destruct (err_below_ceiling s OW LB m HEAP st PL EA PARTS x Hx). lia. }
  split; [exact (lib_cells_agree _ _ _ AG HL HL' HO)|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply (gen_transport2 P _ _ cxo st); [exact HM| exact AG| reflexivity| reflexivity| | auto| auto| auto| auto| auto| | |].
  - intros Ec0 x Hx. apply NM. intros HMx. eapply (cx_not_mont s OW LB m HEAP st PL EA SPX BX PARTS FROK x); eauto.
  - destruct (pl_mont PL) as [[am qm]|] eqn:Em; [|exact I]. left. split; [reflexivity|]. intros x Hx. left.
    destruct PARTS as (_ & _ & _ & (_ & _ & PM) & _). rewrite Em in PM. pose proof (blk_below_ceiling s OW LB m HEAP qm am MONT_CTX_SZ x PM ltac:(lia)). lia.
  - rewrite Ec. right. exact HRC.
  - intros r a HA [Hh|HRp]; [left; exact Hh|]. destruct (in_dec Nat.eq_dec r hs) as [Hi|Hn]; [left; exact Hi|]. right.
    pose proof (gen_ref_valid _ _ _ _ _ _ _ _ S1 HM HA) as HV.
    eapply bn_rep_transport; [exact AG| | | exact HRp]; [|auto].
    intros x Hx. apply NM. intros HMx. destruct Hx as [Hs|[(p & D & Ed & Hin & Hx)|(y & d & Ep & Hx)]].
    + eapply (struct_not_mont s OW LB m HEAP st PL EA SPX BX PARTS FROK r a x); eauto.
    + eapply (limbs_not_mont s OW LB m HEAP st PL EA SPX BX PARTS FROK r p D x); eauto.
    + destruct (pl_of_cases PL r _ Ep) as [[-> E']|[(am & qm & _ & _ & E' & _)|[S Eb]]]; [discriminate E'| discriminate E'|].
      eapply (framebuf_not_mont s OW LB m HEAP st PL EA SPX BX PARTS FROK r y d x); eauto.
Qed.

(* [comment removed for export] *)
Theorem lib_state_set_mont : forall s LB SPX BX cxo hs st m m' OW PL EA am qm ri n0,
  AHEAP s OW LB m -> lib_state_hc cxo hs st m OW PL EA -> frames_ok PL SPX BX -> pl_mont PL = Some (am, qm) ->
  munch [(am + 72, am + MONT_CTX_SZ)] m m' -> wmono ctasegs m m' ->
  rw_cells ctasegs m' (am + 72) (mont_cells (set_mont ri n0 st)) ->
  lib_state_hc cxo hs (set_mont ri n0 st) m' OW PL EA.
Proof.
  intros s LB SPX BX cxo hs st m m' OW PL EA am qm ri n0 HEAP HS FROK Em MU WM HMC.
  pose proof (lib_state_h_parts _ _ _ _ _ _ _ HS) as PARTS. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
  pose proof HS as (HC & (HE1 & HE2) & HO & (S1 & S2 & S3 & HM)).
  destruct PARTS as (WFS & PWF & IDS & (PB & PC & PM) & ERRB). pose proof PM as PM0. rewrite Em in PM.
  pose proof (AH_range _ _ _ _ _ _ _ HEAP PM) as (M0 & _ & _ & MC & MI).
  set (P := fun x => x < am + 72 \/ am + MONT_CTX_SZ <= x).
  assert (AG : agree_on P m m').
  { eapply agree_on_mono; [apply (agree_on_of_munch _ _ _ MU WM)|]. intros x Hx. cbn [outside fst snd]. subst P. cbn beta in Hx. split; [lia| exact I]. }
  assert (NM : forall x, (mont_fp PL x -> False) -> P x).
  { intros x Hx. subst P. cbn beta. destruct (Z.lt_ge_cases x (am + 72)); [left; lia|]. destruct (Z.le_gt_cases (am + MONT_CTX_SZ) x); [right; lia|].
    exfalso. apply Hx. left. exists am, qm. split; [exact Em| lia]. }
  assert (PARTS' : lib_parts st OW PL EA) by (split; [exact WFS| split; [exact PWF| split; [exact IDS| split; [split; [exact PB| split; [exact PC| exact PM0]]| exact ERRB]]]]).
  assert (HL : forall a, ApBnRepA.libw a -> P a).
  { intros a Ha. subst P. cbn beta. pose proof (blk_not_libw s OW LB m HEAP qm am MONT_CTX_SZ a PM) as X.
    destruct (Z.lt_ge_cases a (am + 72)); [left; lia|]. destruct (Z.lt_ge_cases a (am + MONT_CTX_SZ)); [| right; lia].
    exfalso. apply X; [unfold MONT_CTX_SZ in *; lia| apply libw_bn; exact Ha]. }
  assert (HLW : forall a, libw a -> P a).
  { intros a Ha. subst P. cbn beta. pose proof (blk_not_libw s OW LB m HEAP qm am MONT_CTX_SZ a PM) as X.
    destruct (Z.lt_ge_cases a (am + 72)); [left; lia|]. destruct (Z.lt_ge_cases a (am + MONT_CTX_SZ)); [| right; lia].
    exfalso. apply X; [unfold MONT_CTX_SZ in *; lia| exact Ha]. }
  split; [eapply ApBnRepA.crypto_statics_agree; eauto|].
  split. { split; [eapply ApBnRepA.err_statics_agree; eauto|]. eapply ApBnRepA.err_mem_agree; [exact AG| exact HL| | | exact HE2]; [|auto].
           intros x Hx. apply NM. intros HMx. destruct HMx as [(am' & qm' & Em' & Hm')|(c & Ec & Hm')].
           - rewrite Em in Em'. injection Em' as <- <-.
             eapply (err_not_block s OW LB m HEAP st PL EA PARTS' qm am MONT_CTX_SZ x PM); [lia| | exact Hx].
             intros q' Hq'. eapply ids_pl_ea; eauto. eapply in_pl_ids_mont; exact Em.
           - destruct (recp_frame OW st PL EA SPX BX PARTS' FROK c Ec) as (Cc & _).
             destruct (err_below_ceiling s OW LB m HEAP st PL EA PARTS' x Hx). lia. }
  split; [exact (lib_cells_agree _ _ _ AG HL HLW HO)|]. split; [exact S1|]. split; [exact S2|]. split; [exact S3|].
  eapply (gen_transport2 P _ _ cxo st); [exact HM| exact AG| reflexivity| reflexivity| | auto| auto| auto| auto| auto| | |].
  - intros Ec0 x Hx. apply NM. intros HMx. eapply (cx_not_mont s OW LB m HEAP st PL EA SPX BX PARTS' FROK x); eauto.
  - rewrite Em. right. exact HMC.
  - destruct (pl_recp PL) as [c|] eqn:Er; [|exact I]. left. split; [reflexivity|]. intros x Hx. right.
    destruct (recp_frame OW st PL EA SPX BX PARTS' FROK c Er) as (Cc & _). unfold MONT_CTX_SZ in *. lia.
  - intros r a HA [Hh|HRp]; [left; exact Hh|]. destruct (in_dec Nat.eq_dec r hs) as [Hi|Hn]; [left; exact Hi|]. right.
    pose proof (gen_ref_valid _ _ _ _ _ _ _ _ S1 HM HA) as HV.
    eapply bn_rep_transport; [exact AG| | | exact HRp]; [|auto].
    intros x Hx. apply NM. intros HMx. destruct Hx as [Hs|[(p & D & Ed & Hin & Hx)|(y & d & Ep & Hx)]].
    + eapply (struct_not_mont s OW LB m HEAP st PL EA SPX BX PARTS' FROK r a x); eauto.
    + eapply (limbs_not_mont s OW LB m HEAP st PL EA SPX BX PARTS' FROK r p D x); eauto.
    + destruct (pl_of_cases PL r _ Ep) as [[-> E']|[(am' & qm' & _ & _ & E' & _)|[S Eb]]]; [discriminate E'| discriminate E'|].
      eapply (framebuf_not_mont s OW LB m HEAP st PL EA SPX BX PARTS' FROK r y d x); eauto.
Qed.

(* [comment removed for export] *)
Lemma bn_arr_facts_w : forall st OW PL EA SPX BX s LB m r D,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> vref r st -> wref PL r ->
  bn_arr m OW (pl_of PL r) D (getbn r st) ->
  u64arr ctasegs m D (wlimbs (bn_buf (getbn r st)))
  /\ Z.of_nat (length (wlimbs (bn_buf (getbn r st)))) = Z.of_nat (bn_dmax (getbn r st))
  /\ 0 <= D /\ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= ACEIL
  /\ (D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= 0x10000 \/ 0xbcb000 <= D \/ bn_dmax (getbn r st) = 0%nat)
  /\ (forall r' a', ref_at st OW PL r' a' -> a' + 24 <= D \/ D + 8 * Z.of_nat (bn_dmax (getbn r st)) <= a').
Proof.
  intros st OW PL EA SPX BX s LB m r D HEAP PARTS FROK HV WR ARR. pose proof (AH_ceil _ _ _ _ HEAP) as CR. unfold SEGTOP_A, SHHI, STACK_WIN, USTACK_TOP in CR.
  destruct (bn_arr_facts s OW LB m HEAP st PL EA SPX BX PARTS FROK r D HV (proj1 WR) ARR) as (U & LEN & D0 & DC & DI & DSEP).
  split; [exact U|]. split; [exact LEN|]. split; [exact D0|]. split; [|split; [exact DI| exact DSEP]].
  pose proof ARR as ARR'. unfold bn_arr in ARR'. destruct (bn_d (getbn r st)) as [p|] eqn:Ed.
  - destruct ARR' as [Hin _]. pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (_ & _ & _ & BC & _). exact BC.
  - destruct (bn_arr_null PL r m OW D _ (proj1 (proj2 PARTS)) WR Ed ARR) as [-> Eb]. unfold bn_dmax. rewrite Eb. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma struct_client_disj : forall st OW PL EA SPX BX s LB m r a bk,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> frames_ok PL SPX BX -> ref_at st OW PL r a -> r <> ROne -> In bk LB ->
  a + 24 <= blk_addr bk \/ blk_addr bk + blk_size bk <= a.
Proof.
  intros st OW PL EA SPX BX s LB m r a bk HEAP PARTS FROK HA NRO Hbk.
  pose proof (AH_nodup _ _ _ _ HEAP) as ND.
  destruct (skind_cases OW st PL EA SPX BX PARTS FROK r a (ref_at_inb _ _ _ _ _ (proj1 (proj2 PARTS)) (proj1 (proj2 (proj2 (proj2 PARTS)))) HA))
    as [(q & A & n & Hin & R1 & R2 & _)|[(HF & C1 & _)|[-> ->]]]; [| | exfalso; exact (NRO eq_refl)].
  - assert (NE : blk_id (q, A, n) <> blk_id bk).
    { rewrite map_app in ND. intros E. eapply (nodup_app_disj _ _ (blk_id (q, A, n)) ND); [apply in_map; exact Hin| rewrite E; apply in_map; exact Hbk]. }
    pose proof (AH_disjoint_gen _ _ _ _ (q, A, n) bk HEAP ltac:(apply in_or_app; left; exact Hin) ltac:(apply in_or_app; right; exact Hbk) NE) as DJ.
    cbn [blk_addr blk_size fst snd] in DJ |- *. unfold BN_STRUCT_SZ in *. lia.
  - pose proof (AH_range_gen _ _ _ _ _ HEAP ltac:(apply in_or_app; right; exact Hbk)) as (_ & _ & _ & BC & _).
    destruct bk as [[q A] n]. cbn [blk_addr blk_size fst snd] in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition hpl (PL : placement) (r : bnref) : Prop :=
  r <> ROne /\ forall p, pl_of PL r = Some p -> exists a q off, p = PHeap a q off.

Lemma hpl_pool : forall PL i, hpl PL (RPool i).
Proof. intros PL i. split; [unfold RPool, ROne, NFIX; lia|]. intros p. rewrite pl_of_pool. discriminate. Qed.
Lemma hpl_heap : forall PL r a q off, pl_of PL r = Some (PHeap a q off) -> hpl PL r.
Proof.
  intros PL r a q off E. split; [intros ->; rewrite pl_of_one in E; discriminate E|].
  intros p E'. rewrite E in E'. injection E' as <-. exists a, q, off. reflexivity.
Qed.
Lemma hpl_mont : forall PL r am qm, mont_ref r = true -> pl_mont PL = Some (am, qm) -> hpl PL r.
Proof.
  intros PL r am qm M Em. pose proof (pl_of_mont PL r M) as E. rewrite Em in E. eapply hpl_heap. exact E.
Qed.
Lemma hpl_wref : forall PL r, hpl PL r -> wref PL r.
Proof. intros PL r [NE H]. split; [exact NE|]. intros a d E. destruct (H _ E) as (a' & q & off & E'). discriminate E'. Qed.
Lemma hpl_pl_other : forall PL r r' p, r' <> r -> hpl PL r' -> hpl (pl_set PL r p) r'.
Proof. intros PL r r' p NE [N H]. split; [exact N|]. intros p' E. rewrite pl_of_set_other in E by exact NE. exact (H p' E). Qed.
Lemma hpl_pl_ctx : forall PL c r, hpl PL r -> hpl (pl_set_ctx PL c) r.
Proof. intros PL c r [N H]. split; [exact N|]. intros p E. rewrite pl_of_set_ctx in E. exact (H p E). Qed.
Lemma hpl_pl_recp : forall PL rc r, hpl PL r -> hpl (pl_set_recp PL rc) r.
Proof. intros PL rc r [N H]. split; [exact N|]. intros p E. rewrite pl_of_set_recp in E. exact (H p E). Qed.

(* [comment removed for export] *)
Lemma ref_at_hrange : forall st OW PL EA s LB m r a,
  AHEAP s OW LB m -> lib_parts st OW PL EA -> ref_at st OW PL r a -> hpl PL r ->
  0 < a /\ a + 24 <= ACEIL /\ (a + 24 <= 0x10000 \/ 0xbcb000 <= a)
  /\ exists q A n, In (q, A, n) OW /\ A <= a /\ a + 24 <= A + n.
Proof.
  intros st OW PL EA s LB m r a HEAP PARTS HA [NE HH].
  pose proof (ref_at_inb _ _ _ _ _ (proj1 (proj2 PARTS)) (proj1 (proj2 (proj2 (proj2 PARTS)))) HA) as K.
  destruct K as [q n S Eb Hin Hn|am qm M Em Hin Ea Hoff|i q H Er Eq Hin Ea Hj|p S Eb Hiv HF|Er Ea].
  - pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI). unfold BN_STRUCT_SZ in *.
    split; [lia|]. split; [lia|]. split; [lia|]. exists q, a, n. auto with zarith.
  - pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI). unfold MONT_CTX_SZ in *.
    split; [lia|]. split; [lia|]. split; [lia|]. exists qm, am, 96. auto with zarith.
  - pose proof (AH_range _ _ _ _ _ _ _ HEAP Hin) as (B0 & _ & _ & BC & BI). unfold ITEM_SZ, POOL_ITEM_BYTES, BN_CTX_POOL_SIZE in *.
    split; [nia|]. split; [nia|]. split; [nia|]. exists q, H, 400. split; [exact Hin|]. nia.
  - exfalso. rewrite <- (pl_of_stored PL r S) in Eb. destruct (HH p Eb) as (a' & q & off & ->). cbn in Hiv. tauto.
  - exfalso. exact (NE Er).
Qed.

End WithCeiling3.
Arguments lib_state_h_parts {cxo}.
Arguments lib_state_wf {cxo}.
Arguments lib_state_frame {AR} s LB SPX BX {cxo}.
Arguments lib_state_h_ow {cxo}.
Arguments lib_state_h_incl {cxo}.
Arguments ref_at_valid {cxo}.
Arguments lib_state_open {cxo}.
Arguments lib_state_open_ro {cxo}.
Arguments lib_state_close {cxo}.
Arguments lib_state_reclose {cxo}.
Arguments lib_state_h_heap_pres {AR cxo}.
Arguments lib_state_h_free {AR} st LB {cxo}.
Arguments own_fp_lib {AR cxo}.
Arguments own_fp_libA {AR cxo}.
Arguments lib_state_hc_agreeA {cxo}.
Arguments lib_state_h_icall {AR} s LB {cxo}.
Arguments lib_state_h_icall2 {AR} s LB {cxo}.
