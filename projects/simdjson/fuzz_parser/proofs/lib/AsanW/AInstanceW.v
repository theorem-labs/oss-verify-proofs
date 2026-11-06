(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr ITree Nodes Decode InitMem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.LibA Require Import ExecF ITreeA.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib Require Import ADkModel.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AsanW Require Import AImg AProto ABase ARep ALayout AHeapP AMalloc_iface ADepot_iface ADepot ARepQ ARepQP ASec
     ASecFrame F_adepot ADepotW F_adepotW AFake_iface AFake_arep AInstance AInstanceM AInstanceF AInstanceW0 AInstanceFW AMalloc AFreeNull
     F_apoison_remap AHolesD ASF_kit AFreeAll.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Keyed Unification.

Section CANSEC1. Context {rc : runConstT}.
Definition AHEAP_W (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (m : amem) : Prop :=
  AFRESH st /\ exists k, k <= dk st /\ AHEAP_P (AHI_k k) L RNG st LB m.

(* [comment removed for export] *)
Lemma AHW_fresh : forall L RNG st LB m, AHEAP_W L RNG st LB m -> AFRESH st.
Proof. intros L RNG st LB m [HF _]. exact HF. Qed.

Lemma AHW_weak : forall L RNG st LB m, AHEAP_W L RNG st LB m -> AHEAP_P AHI L RNG st LB m.
Proof. intros L RNG st LB m (_ & k & _ & H). exact (AHEAP_k_weak k L RNG st LB m H). Qed.

(* [comment removed for export] *)
Lemma AHW_rng_mono : forall L RNG RNG' st LB m, fp_le RNG RNG' -> AHEAP_W L RNG st LB m -> AHEAP_W L RNG' st LB m.
Proof.
  intros L RNG RNG' st LB m LE (HF & k & Hk & (ALO & ARNG & XB & HFK)). split; [exact HF|]. exists k. split; [exact Hk|].
  split; [exact ALO|]. split; [eapply arng_mono; [exact LE| exact ARNG]|]. split; [exact XB| exact HFK].
Qed.

Lemma AHW_perm : forall L RNG st LB LB' m, Permutation LB LB' -> AHEAP_W L RNG st LB m -> AHEAP_W L RNG st LB' m.
Proof.
  intros L RNG st LB LB' m P (HF & k & Hk & (ALO & ARNG & [X [AR (B1 & B2 & B3 & B4)]] & HFK)). split; [exact HF|]. exists k. split; [exact Hk|].
  split; [exact ALO|]. split; [exact ARNG|]. split.
  - exists X. split; [exact AR|]. split; [| split; [| split]].
    + intros p A n Hin. apply (B1 p A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + intros cls A n Hin. apply (B2 cls A n). eapply Permutation_in; [apply Permutation_sym; exact P| exact Hin].
    + eapply Permutation_NoDup; [apply hb_ids_perm; exact P| exact B3].
    + eapply Permutation_NoDup; [exact P| exact B4].
  - cbn [AHI_k ah_fake] in *. eapply afake_blocks; [exact HFK|]. intros c F n. split; intros H; (eapply Permutation_in; [| exact H]); [apply Permutation_sym; exact P| exact P].
Qed.

Lemma AHW_frame : forall L RNG st LB m m' (W : list ivl),
  AHEAP_W L RNG st LB m -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => aclient_range aci_I LB (ATOP + 4096) (fst iv) (snd iv - fst iv)) W ->
  AHEAP_W L RNG st LB m'.
Proof. intros L RNG st LB m m' W (HF & k & Hk & H) MU WM CW. split; [exact HF|]. exists k. split; [exact Hk|]. exact (AHIk_frame k L RNG st LB m m' W H MU WM CW). Qed.

(* [comment removed for export] *)
Lemma amalloc_post_W : forall k L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms',
  amalloc_post aci_I (AHEAP_P (AHI_k k)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms' ->
  AFRESH (fst r) -> k <= dk (fst r) ->
  amalloc_post aci_I AHEAP_W L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG' ms'.
Proof.
  intros until ms'. intros (LE & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EQ & MI & ST & HP & SN) HF Hk.
  split; [exact LE|]. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [exact EQ|]. split; [exact MI|]. split; [exact ST|]. split; [exact HP|].
  destruct (snd r) as [p|]; [| exact SN]. destruct SN as (A & junk & H1 & H2 & AH & H3).
  exists A, junk. split; [exact H1|]. split; [exact H2|]. split; [split; [exact HF| exists k; split; [exact Hk| exact AH]]| exact H3].
Qed.

Lemma afree_post_W : forall k L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m r RNG' ms',
  afree_post aci_I (AHEAP_P (AHI_k k)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m r RNG' ms' ->
  AFRESH r -> k <= dk r ->
  afree_post aci_I AHEAP_W L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m r RNG' ms'.
Proof.
  intros until ms'. intros (LE & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EQ & MI & ST & HP & AH) HF Hk.
  split; [exact LE|]. exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [exact EQ|]. split; [exact MI|]. split; [exact ST|]. split; [exact HP|]. split; [exact HF|]. exists k. split; [exact Hk| exact AH].
Qed.

Lemma afree_null_post_W : forall k L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m ms',
  afree_null_post aci_I (AHEAP_P (AHI_k k)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m ms' ->
  AFRESH st -> k <= dk st ->
  afree_null_post aci_I AHEAP_W L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB lo m ms'.
Proof.
  intros until ms'. intros (t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EQ & MI & ST & HP & AH) HF Hk.
  exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'.
  split; [exact EQ|]. split; [exact MI|]. split; [exact ST|]. split; [exact HP|]. split; [exact HF|]. exists k. split; [exact Hk| exact AH].
Qed.

(* [comment removed for export] *)
Lemma AHk_malloc : forall k, amalloc_stmt aci_I (AHEAP_P (AHI_k k)).
Proof. intros k. exact (amalloc_all (DI_of k) AQUAR AFAKE (AHI_k_laws k) poison_remap_proof aci_I aci_ok aci_ok2). Qed.

Theorem AHW_malloc : amalloc_stmt aci_I AHEAP_W.
Proof.
  unfold amalloc_stmt. intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB n lo tr RESV
    (HF & k & Hk & AH). intros.
  eapply implF_epost_mono.
  { eapply implF_embed_sallA; [eapply (AHk_malloc k); eauto| exact (amalloc_fresh_dk ATOP RESV st n HF)]. }
  intros r RNG' ms' [PO [F1 D]]. eapply amalloc_post_W; [exact PO| exact F1| lia].
Qed.

Lemma AHk_free_null : forall k, afree_null_stmt aci_I (AHEAP_P (AHI_k k)).
Proof. intros k. exact (afree_nullP (DI_of k) ASEC_of AFAKE (AHI_k_laws k) aci_I aci_okQ). Qed.

Theorem AHW_free_null : afree_null_stmt aci_I AHEAP_W.
Proof.
  unfold afree_null_stmt. intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB lo tr
    (HF & k & Hk & AH). intros.
  eapply evtF_mono; [eapply (AHk_free_null k); eauto|]. intros ms' PO. eapply afree_null_post_W; [exact PO| exact HF| exact Hk].
Qed.

(* [comment removed for export] *)
Lemma adepotk_frameD : forall k, depot_frameD_law (ADEPOT (DI_of k)).
Proof.
  intros k. unfold depot_frameD_law. cbn [ADEPOT DI_of]. intros L m m' W (D & w & WFW & Hw & HL & DC & LY) MU FA.
  exists D, w. split; [exact WFW|]. split; [exact Hw|]. split; [exact HL|]. split; [| exact LY].
  pose proof (adepot_frameD L m m' W (ex_intro _ D (conj (proj1 WFW) (conj DC LY))) MU FA) as _.
  pose proof LY as (_ & _ & LN0 & LN1 & LS0 & LS1 & _). unfold AIMG_HI in *.
  pose proof (proj1 WFW) as (N1 & LK & HD & ND & CMP & TF0 & TFB & NB).
  pose proof (CNT_nonneg (al_U L) (dhs D) (Z.to_nat (dN D))) as CN.
  assert (OUT : forall x, (0x1e19c8 <= x < 0x631a10 \/ al_nodes L <= x < al_nodes L + 1048576 \/ al_store L <= x < al_store L + 8388608) ->
                         m' (wa x) = m (wa x)).
  { intros x Hx. apply (munch_point W m m' x MU); [lia|].
    clear - FA Hx. induction FA as [| [lo hi] W Hiv FA IH]; cbn; [exact I|]. split; [| exact IH].
    intros Hin. destruct (Hiv x Hin) as (A & B & C). cbn in *. lia. }
  destruct DC as (C1 & C2 & C3 & C4 & C5 & CT & CN' & SK1 & SK2).
  unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in *.
  split; [eapply rw_cells_agreeD; [exact C1| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C2| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C3| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C4| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split; [eapply rw_cells_agreeD; [exact C5| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]|].
  split. { intros b Hb. eapply rw_cells_agreeD; [exact (CT b Hb)| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]. }
  split. { intros i Hi. eapply rw_cells_agreeD; [exact (CN' i Hi)| intros x Hx; apply OUT; unfold SSTF, SSPTR, SSST, NUNIQ, MAP1, TAB in Hx; cbn in Hx; lia]. }
  split. { eapply stk_agreeD; [exact SK1| intros x Hx; apply OUT; lia]. }
  eapply stk_agreeD; [exact SK2| intros x Hx; apply OUT; lia].
Qed.

Lemma AHk_free : forall k, afree_stmt aci_I (AHEAP_P (AHI_k k)).
Proof. intros k. exact (afree_total (DI_of k) AFAKE (AHI_k_laws k) aci_I aci_okQ aci_ok2 (adepotk_frameD k) afake_frameD). Qed.

Theorem AHW_free : afree_stmt aci_I AHEAP_W.
Proof.
  unfold afree_stmt. intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo tr
    (HF & k & Hk & AH) HIN. intros.
  eapply implF_epost_mono.
  { eapply implF_embed_sallA; [eapply (AHk_free k); eauto| exact (afree_fresh_dk st (Some p) HF)]. }
  intros r RNG' ms' [PO [F1 D]]. eapply afree_post_W; [exact PO| exact F1| lia].
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qhdrs_ext : forall L u chs ks, qhdrs (ext L u) chs ks = qhdrs L chs ks.
Proof. intros L u chs. induction chs as [|ch chs IH]; intros [|k ks]; cbn [qhdrs]; try reflexivity. rewrite IH. reflexivity. Qed.

Lemma abatches_to_ext : forall L u m bs qs nxt, abatches_to L m bs qs nxt -> abatches_to (ext L u) m bs qs nxt.
Proof.
  intros L u m bs. induction bs as [|b bs IH]; intros [|q qs] nxt H; cbn [abatches_to] in *; try exact H.
  destruct H as [A B]. split; [| exact (IH qs nxt B)]. unfold abatch_cells in *. rewrite qhdrs_ext. exact A.
Qed.
Lemma abatches_to_shr : forall L u m bs qs nxt, abatches_to (ext L u) m bs qs nxt -> abatches_to L m bs qs nxt.
Proof.
  intros L u m bs. induction bs as [|b bs IH]; intros [|q qs] nxt H; cbn [abatches_to] in *; try exact H.
  destruct H as [A B]. split; [| exact (IH qs nxt B)]. unfold abatch_cells in *. rewrite qhdrs_ext in A. exact A.
Qed.

Lemma AQUAR_ext : forall L u st X m, AQUAR L st X m -> AQUAR (ext L u) st X m.
Proof.
  intros L u st X m (Q & G & [R1 A1] & [R2 A2] & IA & QC & QN). exists Q.
  split; [exact G|]. split; [split; [exact R1| exact (abatches_to_ext L u m _ _ 0 A1)]|].
  split; [split; [exact R2| exact (abatches_to_ext L u m _ _ 0 A2)]|]. split; [exact IA|]. split; [exact QC| exact QN].
Qed.
Lemma AQUAR_shr : forall L u st X m, AQUAR (ext L u) st X m -> AQUAR L st X m.
Proof.
  intros L u st X m (Q & G & [R1 A1] & [R2 A2] & IA & QC & QN). exists Q.
  split; [exact G|]. split; [split; [exact R1| exact (abatches_to_shr L u m _ _ 0 A1)]|].
  split; [split; [exact R2| exact (abatches_to_shr L u m _ _ 0 A2)]|]. split; [exact IA|]. split; [exact QC| exact QN].
Qed.

Lemma ASEC_of_ext : forall L u st X m, alayout_ok (ext L u) -> ASEC_of L st X m -> ASEC_of (ext L u) st X m.
Proof.
  intros L u st X m ALO ((_ & W2 & W3 & W4 & W5 & W6 & W7) & AR & AI & AP & AZ).
  exact (conj (conj ALO (conj W2 (conj W3 (conj W4 (conj W5 (conj W6 W7)))))) (conj AR (conj AI (conj AP AZ)))).
Qed.
Lemma ASEC_of_shr : forall L u st X m, alayout_ok L -> ASEC_of (ext L u) st X m -> ASEC_of L st X m.
Proof.
  intros L u st X m ALO ((_ & W2 & W3 & W4 & W5 & W6 & W7) & AR & AI & AP & AZ).
  exact (conj (conj ALO (conj W2 (conj W3 (conj W4 (conj W5 (conj W6 W7)))))) (conj AR (conj AI (conj AP AZ)))).
Qed.

(* [comment removed for export] *)
Lemma AHEAP_k_ext : forall k L RNG st LB m u, AHEAP_P (AHI_k k) L RNG st LB m -> k < DWMAX -> (length u <= 255)%nat ->
  AHEAP_P (AHI_k (k + 1)) (ext L u) RNG st LB m.
Proof.
  intros k L RNG st LB m u (ALO & ARNG & [X [AR BL]] & HFK) Hk Hu.
  pose proof (AREP_k_depot k L st X m AR) as HD. pose proof HD as (D & w & _ & _ & HLEN & _).
  assert (ALO' : alayout_ok (ext L u)).
  { destruct ALO. constructor; try assumption. cbn [ext al_U length]. unfold AUMAX, DWMAX in *. lia. }
  split; [exact ALO'|]. split; [exact ARNG|]. split; [| exact HFK]. exists X. split; [| exact BL].
  pose proof (AREP_k_weak k L st X m AR) as (WF & RT & INST & THR & CLS & HQ & HS & _ & HRO & RT2 & AVL & RT3).
  exact (conj WF (conj RT (conj INST (conj THR (conj CLS (conj (AQUAR_ext L u st X m HQ) (conj (ASEC_of_ext L u st X m ALO' HS) (conj (adepotk_ext L k m u HD Hk Hu) (conj HRO (conj RT2 (conj AVL RT3))))))))))).
Qed.

Lemma AHEAP_k_shrink : forall k L RNG st LB m u, AHEAP_P (AHI_k k) (ext L u) RNG st LB m -> AHEAP_P (AHI_k k) L RNG st LB m.
Proof.
  intros k L RNG st LB m u (ALO & ARNG & [X [AR BL]] & HFK).
  assert (ALO' : alayout_ok L).
  { pose proof (ao_U _ ALO) as HU. cbn [ext al_U length] in HU. destruct ALO. constructor; try assumption. lia. }
  split; [exact ALO'|]. split; [exact ARNG|]. split; [| exact HFK]. exists X. split; [| exact BL].
  pose proof (AREP_k_depot k (ext L u) st X m AR) as HD.
  pose proof (AREP_k_weak k (ext L u) st X m AR) as (WF & RT & INST & THR & CLS & HQ & HS & _ & HRO & RT2 & AVL & RT3).
  exact (conj WF (conj RT (conj INST (conj THR (conj CLS (conj (AQUAR_shr L u st X m HQ) (conj (ASEC_of_shr L u st X m ALO' HS) (conj (adepotk_shrink L k m u HD) (conj HRO (conj RT2 (conj AVL RT3))))))))))).
Qed.

(* [comment removed for export] *)
Definition aunwW (m : amem) (L : alayout) (RNG : footprint) (lo PC : Z) (sp s0 ra : word) (tr : list Z) : Prop :=
  bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) PC (bv_unsigned sp) (bv_unsigned s0) UDEPTH tr /\ (length tr <= 28)%nat
  /\ rng RNG lo (al_top L - lo).

Theorem AHW_free_wild : forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (p : aptr) (A n lo : Z) (tr : list Z),
  AHEAP_W L RNG st LB m -> In (HB p A n) LB ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AFREE_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 A ->
  aunwW m L RNG lo AFREE_PC sp s0 ra tr -> dk st < DWMAX ->
  bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AFREE_PC ->
  bv_unsigned sp mod 16 = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  implS asegs RNG (aembed ATOP (afree st (Some p)))
        (epostF (afree_post aci_I AHEAP_W L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB p lo m))
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AFREE_SYM) fc None m (seg_rom asegs)).
Proof.
  intros L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st LB p A n lo tr
    (HF & k & Hk & AH) HIN MI ST LO1 LO2 TP A0 (U1 & U2 & U3 & U4) DK NS RA RAPC SP16 RLO.
  destruct (AHI_chunk L RNG st LB m p A n (AHEAP_k_weak k _ _ _ _ _ AH) HIN) as (ch & Hch & _).
  set (u := AFREE_PC :: bv_unsigned ra :: tr).
  assert (LU : (length u <= 255)%nat) by (unfold u; cbn [length]; lia).
  pose proof (AHEAP_k_ext k L RNG st LB m u AH ltac:(lia) LU) as AH'.
  assert (UW : aunw m (ext L u) RNG lo AFREE_PC sp s0 ra tr).
  { left. split; [exact U1|]. split; [exact U2|]. split; [exact U3|]. split; [cbn [ext al_U]; left; reflexivity| exact U4]. }
  eapply implF_epost_mono.
  { eapply implF_embed_sallA; [eapply (AHk_free (k + 1) (ext L u)); eauto| exact (sallA_and _ _ _ (afree_dk st p ch Hch) (afree_fresh_dk st (Some p) HF))]. }
  intros r RNG' ms' [PO [D [F1 _]]].
  destruct PO as (LE & x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & x14 & m' & EQ & MI' & ST' & HP & AH2).
  split; [exact LE|]. exists x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, m'.
  split; [exact EQ|]. split; [exact MI'|]. split; [exact ST'|]. split; [exact HP|].
  split; [exact F1|]. exists (k + 1). split; [lia| exact (AHEAP_k_shrink (k + 1) L RNG' r (lb_remove p LB) m' u AH2)].
Qed.
End CANSEC1.
