(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Nodes Decode.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AS Require Import BackingAlgebra.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanCtrlProps Gap AsanInv AsanBudget AsanTotalCore AsanNodeSem AsanPlace.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Scfg Require Import EdDefs.
Unset Nia Cache. Unset Nra Cache.
Unset Lia Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithResv.
Context {RESV : list (Z * Z)} {ATOP : Z}.
Local Notation INV := (AsanInv.INV RESV ATOP).
Local Notation AMI := (AsanInv.AMI RESV ATOP).
Local Notation AINV := (AsanInv.AINV ATOP).
Local Notation aok := (AsanNodeSem.aok ATOP).
Local Notation apost := (AsanNodeSem.apost ATOP).
Local Notation atot := (atotal aok apost).
Local Notation chunk_wf := (AsanInv.chunk_wf ATOP).

Lemma INV_atop : forall pc pb st mo, INV pc pb st mo -> atop_ok ATOP /\ alloc_top (m_vmmaps mo) = ATOP.
Proof. intros pc pb st mo [_ HM]. exact (AMI_atop _ _ _ HM). Qed.

Lemma region_free_sub : forall l (a n a' n' : Z),
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  0 <= a -> a <= a' -> 0 <= n' -> a' + n' <= a + n -> a + n < 2^64 ->
  region_free l (Z_to_bv 64 a') (Z_to_bv 64 n') = true.
Proof.
  induction l as [|[b sz] l IH]; intros a n a' n' H Ha Haa Hn Hsub Htop; [reflexivity|].
  cbn [region_free] in H |- *. apply andb_prop in H as [H1 H2]. rewrite (IH _ _ _ _ H2 Ha Haa Hn Hsub Htop), andb_true_r.
  unfold iv_overlap in *. rewrite !unsigned_lit in H1 |- * by lia.
  apply negb_true_iff in H1. apply negb_true_iff. apply andb_false_iff in H1. apply andb_false_iff.
  destruct H1 as [H1|H1]; apply Z.ltb_ge in H1; [left|right]; apply Z.ltb_ge; lia.
Qed.

Definition same_but (c : Z) (st st' : astate) : Prop :=
  a_space_beg st' = a_space_beg st /\ a_ptr_array st' = a_ptr_array st /\ a_nres st' = a_nres st /\ a_nsec st' = a_nsec st
  /\ a_cinit st' = a_cinit st /\ a_live st' = a_live st /\ a_next st' = a_next st
  /\ a_qloc st' = a_qloc st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob st' = a_qglob st /\ a_qglob_bytes st' = a_qglob_bytes st
  /\ (forall c', c' <> c -> get_cls st' c' = get_cls st c')
  /\ a_emb st' = a_emb st.

Lemma same_but_refl : forall c st, same_but c st st.
Proof. intros. unfold same_but. repeat split; reflexivity. Qed.

Definition cls_keep (X : Z) (st st' : astate) : Prop :=
  forall c, c <> X -> c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) /\ c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c).
Definition malloc_cls (n : Z) : Z := if is_primary n then class_id (needed_size n) else K_BATCH_CLASS.
Lemma cls_keep_refl : forall X st, cls_keep X st st.
Proof. intros X st c _. split; reflexivity. Qed.
Lemma cls_keep_same_but : forall c st st', same_but c st st' -> cls_keep c st st'.
Proof. intros c st st' SB c' Hc'. destruct SB as (_&_&_&_&_&_&_&_&_&_&_&G&_). rewrite (G c' Hc'). split; reflexivity. Qed.
Lemma cls_keep_cls_eq : forall X st st', a_cls st' = a_cls st -> cls_keep X st st'.
Proof. intros X st st' E c _. unfold get_cls. rewrite E. split; reflexivity. Qed.
Lemma cls_keep_trans : forall X s1 s2 s3, cls_keep X s1 s2 -> cls_keep X s2 s3 -> cls_keep X s1 s3.
Proof. intros X s1 s2 s3 A B c Hc. destruct (A c Hc) as [A1 A2]. destruct (B c Hc) as [B1 B2]. split; congruence. Qed.

Definition ucnt_keep (st st' : astate) : Prop :=
  forall c, c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) /\ c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c).
Lemma ucnt_keep_refl : forall st, ucnt_keep st st.
Proof. intros st c. split; reflexivity. Qed.
Lemma ucnt_keep_trans : forall s1 s2 s3, ucnt_keep s1 s2 -> ucnt_keep s2 s3 -> ucnt_keep s1 s3.
Proof. intros s1 s2 s3 A B c. destruct (A c) as [A1 A2]. destruct (B c) as [B1 B2]. split; congruence. Qed.
Lemma ucnt_cls_keep : forall X st st', ucnt_keep st st' -> cls_keep X st st'.
Proof. intros X st st' U c _. exact (U c). Qed.
Lemma ucnt_keep_cls_eq : forall st st', a_cls st' = a_cls st -> ucnt_keep st st'.
Proof. intros st st' E c. unfold get_cls. rewrite E. split; reflexivity. Qed.
Lemma same_but_put : forall c st r, same_but c st (put_cls c r st).
Proof. intros. unfold same_but. repeat split; try reflexivity. intros c' Hc'. apply get_put_ne. congruence. Qed.
Lemma same_but_trans : forall c st1 st2 st3, same_but c st1 st2 -> same_but c st2 st3 -> same_but c st1 st3.
Proof.
  intros c st1 st2 st3 A B. unfold same_but in *.
  destruct A as (?&?&?&?&?&?&?&?&?&?&?&HA&?). destruct B as (?&?&?&?&?&?&?&?&?&?&?&HB&?).
  repeat split; try congruence. intros c' Hc'. rewrite HB, HA; auto.
Qed.

Lemma INV_set_exh : forall pc pb v st mo, INV pc pb (set_exh v st) mo <-> INV pc pb st mo.
Proof. intros. split; intros H; exact H. Qed.
Lemma same_but_set_exh : forall c v st, same_but c st (set_exh v st).
Proof. intros. unfold same_but. repeat split; reflexivity. Qed.

Definition CLSOK (pc : list achunk) (pb : list abatch) (st : astate) (c : Z) (r : aclass) : Prop :=
  0 <= c_allocated_user r /\ c_allocated_user r <= c_mapped_user r /\ c_mapped_user r <= K_FREEARR_OFF
  /\ c_mapped_user r - c_allocated_user r <= 2 * K_USER_MAP
  /\ c_mapped_user r mod K_USER_MAP = 0
  /\ 0 <= c_mapped_free_array r <= K_FREEARR_MAX /\ c_mapped_free_array r mod K_FREEARR_MAP = 0
  /\ 0 <= c_num_freed r /\ 0 <= c_count r <= max_count st c
  /\ c_allocated_user r = size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + c_count r + c_num_freed r).

Lemma AINV_cls : forall pc pb st c, AINV pc pb st -> 1 <= c <= 31 -> CLSOK pc pb st c (get_cls st c).
Proof. intros pc pb st c (H & _) Hc. exact (H c Hc). Qed.

Lemma AINV_put_cls : forall pc pb st c r, AINV pc pb st -> 1 <= c <= 31 -> CLSOK pc pb st c r -> AINV pc pb (put_cls c r st).
Proof.
  intros pc pb st c r H Hc HR. unfold AINV in *. rewrite !all_chunks_put, !qbatches_put, !CH_put.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9). cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array put_cls set_cls] in *.
  split; [| repeat (split; [assumption|]); assumption].
  intros c' Hc'. unfold cls_inv. rewrite max_count_put, all_chunks_put, qbatches_put.
  destruct (Z.eq_dec c' c) as [->|Hne].
  - rewrite get_put_eq. exact HR.
  - rewrite get_put_ne by congruence. exact (HC c' Hc').
Qed.

Lemma csum_bound : forall f st b, (forall c, 1 <= c <= 31 -> f (get_cls st c) <= b) -> csum f st <= 31 * b.
Proof.
  intros f st b H. unfold csum.
  assert (G : forall l, (forall c, In c l -> 1 <= c <= 31) -> fold_right (fun c acc => f (get_cls st c) + acc) 0 l <= zlen l * b).
  { induction l as [|c l IH]; intros Hl; unfold zlen in *; cbn [fold_right length]; [lia|]. rewrite Nat2Z.inj_succ.
    pose proof (H c (Hl c (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
  specialize (G CLASSES ltac:(intros c Hc; apply In_CLASSES; exact Hc)). change (zlen CLASSES) with 31 in G. exact G.
Qed.
Lemma csum_nonneg : forall f st, (forall c, 1 <= c <= 31 -> 0 <= f (get_cls st c)) -> 0 <= csum f st.
Proof.
  intros f st H. unfold csum.
  assert (G : forall l, (forall c, In c l -> 1 <= c <= 31) -> 0 <= fold_right (fun c acc => f (get_cls st c) + acc) 0 l).
  { induction l as [|c l IH]; intros Hl; cbn [fold_right]; [lia|].
    pose proof (H c (Hl c (or_introl eq_refl))). specialize (IH ltac:(intros; apply Hl; right; assumption)). lia. }
  apply G. intros c Hc; apply In_CLASSES; exact Hc.
Qed.

Definition CBMAX : Z := 31 * (K_FREEARR_OFF + K_FREEARR_MAX) + 8 * (64 * K_CHUNKS_BLOCK).
Lemma commit_bytes_bound : forall pc pb st, AINV pc pb st -> 0 <= commit_bytes st <= CBMAX.
Proof.
  intros pc pb st H. pose proof H as (HC & _ & _ & _ & _ & _ & Hres & _).
  unfold commit_bytes, CBMAX.
  pose proof (csum_bound cls_mapped_bytes' st (K_FREEARR_OFF + K_FREEARR_MAX)) as B1.
  pose proof (csum_nonneg cls_mapped_bytes' st) as B0.
  assert (A : forall c, 1 <= c <= 31 -> 0 <= cls_mapped_bytes' (get_cls st c) <= K_FREEARR_OFF + K_FREEARR_MAX).
  { intros c Hc. destruct (HC c Hc) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10). unfold cls_mapped_bytes'. lia. }
  specialize (B1 ltac:(intros c Hc; apply A; exact Hc)). specialize (B0 ltac:(intros c Hc; apply A; exact Hc)).
  unfold K_CHUNKS_BLOCK in *. destruct Hres as (j & Hj & ->). lia.
Qed.

Lemma mmap_len_id : forall l, 0 <= l -> l mod 4096 = 0 -> mmap_len l = l.
Proof.
  intros l Hl Hm. unfold mmap_len, page_round_up_Z, page_size.
  pose proof (Z.div_mod l 4096 ltac:(lia)). rewrite Hm in H.
  replace (l + 4096 - 1) with (l / 4096 * 4096 + 4095) by lia.
  rewrite Z.div_add_l by lia. change (4095 / 4096) with 0. lia.
Qed.

Lemma region_free_above : forall l (a n : Z) R,
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= R) l -> R <= a -> 0 <= a -> a + n < 2^64 -> 0 <= n ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros a n R Hf HR Ha Han Hn; [reflexivity|].
  apply Forall_cons_iff in Hf as [H1 Hf]. cbn [region_free]. rewrite (IH a n R Hf HR Ha Han Hn).
  unfold iv_overlap. rewrite !unsigned_lit by lia. cbn [fst snd] in H1.
  replace (a <? bv_unsigned b + bv_unsigned s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma CH_wf : forall pc pb st, AINV pc pb st -> Forall (fun e => 0 <= snd e < 2^64) (CH pc pb st).
Proof.
  intros pc pb st (_ & Hwf & _). unfold CH. induction (all_chunks pc pb st) as [|ch l IH]; [constructor|].
  apply Forall_cons_iff in Hwf as [H1 Hwf]. rewrite secs_cons. apply Forall_app. split; [|apply IH; exact Hwf].
  destruct ch as [c n|mb ms n]; cbn [sec_of]; [constructor|]. constructor; [|constructor]. cbn [snd].
  cbn [chunk_wf] in H1. destruct H1 as (Hn & -> & _). pose proof (sec_map_size_bounds n ltac:(lia)). lia.
Qed.

Lemma emb_ent_wf : forall pc pb st, AINV pc pb st -> Forall (fun e => 0 <= snd e < 2^64) (emb_ent st).
Proof.
  intros pc pb st HA. destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE). unfold emb_ok in HE. unfold emb_ent.
  destruct (a_emb st) as [[d cap] sz]. destruct (Z.eqb_spec cap 0); [constructor|]. destruct HE as [[E _]|(E1 & _)]; [lia|].
  constructor; [| constructor]. cbn [snd]. unfold EMB_INIT, EMB_MAX in E1. lia.
Qed.
Lemma CHX_wf : forall pc pb st, AINV pc pb st -> Forall (fun e => 0 <= snd e < 2^64) (CHX pc pb st).
Proof. intros pc pb st HA. unfold CHX. apply Forall_app. split; [exact (CH_wf _ _ _ HA)| exact (emb_ent_wf _ _ _ HA)]. Qed.
Lemma CHX_put : forall pc pb c r st, CHX pc pb (put_cls c r st) = CHX pc pb st. Proof. reflexivity. Qed.
Lemma CHX_init_cache : forall pc pb st, CHX pc pb (init_cache st) = CHX pc pb st.
Proof. intros. unfold init_cache. destruct (a_cinit st); reflexivity. Qed.
Lemma zsum2_CHX : forall pc pb st, zsum2 (CHX pc pb st) = zsum2 (CH pc pb st) + zsum2 (emb_ent st).
Proof. intros. unfold CHX. apply zsum2_app. Qed.
Lemma emb_ent_zsum2 : forall pc pb st, AINV pc pb st -> 0 <= zsum2 (emb_ent st) <= EMB_MAX.
Proof.
  intros pc pb st HA. destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE). unfold emb_ok in HE. unfold emb_ent.
  destruct (a_emb st) as [[d cap] sz]. destruct (Z.eqb_spec cap 0); [cbn; unfold EMB_MAX; lia|]. destruct HE as [[E _]|(E1 & _)]; [lia|].
  cbn [zsum2 snd]. unfold EMB_INIT in E1. lia.
Qed.

Lemma CHX_bounds : forall pc pb st,
  AINV pc pb st -> bsum (qbatches pb st) <= 2^30 -> zlen (secs pc) <= 2 -> secbytes pc <= 2^32 ->
  zsum2 (CHX pc pb st) <= 2^37.
Proof.
  intros pc pb st HA HQ H1 H2. destruct (CH_bounds pc pb st HA HQ H1 H2) as [_ X]. pose proof (emb_ent_zsum2 _ _ _ HA) as EZ.
  rewrite zsum2_CHX. unfold EMB_MAX in EZ. lia.
Qed.

Lemma INV_backing_bound : forall pc pb st mo, INV pc pb st mo ->
  vm_backing_used mo <= EAGER0 + CBMAX + zsum2 (CHX pc pb st).
Proof.
  intros pc pb st mo [HA HM]. pose proof (AMI_nonlazy_bound _ _ _ HM (CHX_wf _ _ _ HA)).
  pose proof (commit_bytes_bound _ _ _ HA). rewrite vm_backing_used_split. destruct HM as (-> & _). cbn [length Z.of_nat]. lia.
Qed.

Lemma INV_fixed_aok : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E ->
  region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 len) = true -> 0 < a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> zsum2 (CHX pc pb st) <= 2^37 ->
  aok (AMmap a len PROT_RW F_FIXED) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Ha0 Hal Hll Hlen HSB.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold RES_HI, ACEIL, ATOP_MAX in *. unfold B, S in *. pose proof (bv_unsigned_in_range 64 (fst E)) as HE0.
  assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
  cbn [AsanNodeSem.aok]. split; [reflexivity|]. split; [lia|]. split; [exact T3|].
  replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite ML. split; [left; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|split].
  - exact HR.
  - apply (map_contains_In _ E); auto; rewrite !unsigned_lit by lia; lia.
  - apply mmap_fixed_rw_budget_ok_commit_intro; [reflexivity| exact Hwf|].
    rewrite !unsigned_lit by lia. rewrite M2. unfold LIMIT.
    pose proof (INV_backing_bound _ _ _ _ HI).
    pose proof (overlap_sum_contained (vm_maps (m_vmmaps mo)) E a (a + len) (proj1 M9) HinE ltac:(unfold B; lia) ltac:(unfold B, S; lia) ltac:(lia)).
    unfold EAGER0, CBMAX, K_FREEARR_OFF, K_FREEARR_MAX, K_CHUNKS_BLOCK in *. lia.
Qed.

Lemma INV_resv_hi : forall pc pb st mo, INV pc pb st mo ->
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= RES_HI) (vm_reserved (m_vmmaps mo)).
Proof. intros pc pb st mo [_ HM]. destruct HM as (_ & _ & M3 & _). exact M3. Qed.

Lemma INV_fixed_aok_high : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E -> RES_HI <= a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> zsum2 (CHX pc pb st) <= 2^37 ->
  aok (AMmap a len PROT_RW F_FIXED) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Hal Hll Hlen HSB.
  pose proof HI as [HA HM]. pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold ACEIL, ATOP_MAX in T1, T2. unfold B, S in HE1, HE2. unfold RES_HI in HR.
  apply (INV_fixed_aok pc pb st mo E a len HI HinE); unfold B, S; auto; try lia.
  apply (region_free_above _ a len RES_HI M3); unfold RES_HI in *; lia.
Qed.

Lemma INV_recommit_aok : forall pc pb st mo E a len,
  INV pc pb st mo -> In E (vm_maps (m_vmmaps mo)) -> B E <= a -> a + len <= B E + S E -> RES_HI <= a ->
  a mod 4096 = 0 -> len mod 4096 = 0 -> 0 < len <= 2^30 -> zsum2 (CHX pc pb st) <= 2^37 ->
  aok (AMmap a len PROT_RW F_FIXNORES) mo.
Proof.
  intros pc pb st mo E a len HI HinE HE1 HE2 HR Hal Hll Hlen HSB.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & _).
  assert (HEok : bv_unsigned (fst E) + bv_unsigned (snd E) <= ATOP) by (destruct (proj1 (Forall_forall _ _) M6 E HinE) as (_ & _ & _ & ?); assumption).
  unfold RES_HI, ACEIL, ATOP_MAX in *. unfold B, S in *. pose proof (bv_unsigned_in_range 64 (fst E)) as HE0.
  assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
  cbn [AsanNodeSem.aok]. split; [reflexivity|]. split; [lia|]. split; [exact T3|].
  replace (a =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite ML. split; [right; reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [|split].
  - apply (region_free_above _ a len 0x7fff7000); auto; try lia.
  - apply (map_contains_In _ E); auto; rewrite !unsigned_lit by lia; lia.
  - apply mmap_fixed_rw_budget_ok_recommit_intro; [reflexivity| exact Hwf| | | | |];
      rewrite ?unsigned_lit by lia; unfold page_size; try lia.
    rewrite M2. unfold LIMIT. pose proof (INV_backing_bound _ _ _ _ HI). unfold EAGER0, CBMAX, K_FREEARR_OFF, K_FREEARR_MAX, K_CHUNKS_BLOCK in *. lia.
Qed.

Lemma INV_munmap_aok : forall pc pb st mo mb ms,
  INV pc pb st mo -> In (mb, ms) (CHX pc pb st) ->
  0 < mb -> mb mod 4096 = 0 -> 0 < ms <= 2^32 -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  aok (AMunmap mb ms) mo.
Proof.
  intros pc pb st mo mb ms [HA HM] Hin Hmb Hal Hms Hml Hce.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB & HLZ).
  assert (ML : mmap_len ms = ms) by (apply mmap_len_id; lia).
  cbn [AsanNodeSem.aok]. rewrite ML. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  apply map_has_In. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. right.
  change (Z_to_bv 64 mb, Z_to_bv 64 ms) with (went (mb, ms)). apply in_map. exact Hin.
Qed.

Lemma live_bytes_perm' : forall l l', Permutation l l' -> live_bytes l = live_bytes l'.
Proof. intros. rewrite !live_bytes_sum_count. apply sum_count_perm. assumption. Qed.
Lemma live_bytes_app' : forall l1 l2, live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. intros. apply BackingAlgebra.live_bytes_app. Qed.

Lemma INV_grant_aok : forall pc pb st mo n,
  INV pc pb st mo -> 64512 < n <= 2^32 - 2^20 -> zsum2 (CHX pc pb st) <= 2^37 ->
  aok (AMmapT (sec_map_size n)) mo.
Proof.
  intros pc pb st mo n HI Hn HSB.
  pose proof HI as [HA HM].
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & L0 & HP & HS & HB & HLZ).
  pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (ML : mmap_len (sec_map_size n) = sec_map_size n).
  { apply mmap_len_id; [lia|]. unfold sec_map_size, rup, PG.
    match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end.
    apply Z_mod_mult. }
  cbn [AsanNodeSem.aok]. rewrite ML. split; [lia|]. split; [exact T3|].
  rewrite M2. unfold LIMIT. pose proof (INV_backing_bound _ _ _ _ HI). unfold EAGER0, CBMAX, K_FREEARR_OFF, K_FREEARR_MAX, K_CHUNKS_BLOCK in *. lia.
Qed.

Lemma INV_grant_emb_aok : forall pc pb st mo len,
  INV pc pb st mo -> 0 < len <= EMB_MAX + 4096 -> len mod 4096 = 0 -> zsum2 (CHX pc pb st) <= 2^37 -> zlen (CHX pc pb st) <= SMAX + 2^15 + 1 ->
  aok (AMmap 0 len PROT_RW F_ANON) mo.
Proof.
  intros pc pb st mo len HI Hlen Hl4 HSB HSL.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & L0 & HP & HS & HB & HLZ).
  assert (ML : mmap_len len = len) by (apply mmap_len_id; lia).
  unfold EMB_MAX in Hlen.
  cbn [AsanNodeSem.aok]. rewrite Z.eqb_refl. rewrite ML. split; [reflexivity|]. split; [lia|]. split; [exact T3|]. split; [reflexivity|]. split.
  - rewrite M2. unfold LIMIT. pose proof (INV_backing_bound _ _ _ _ HI). unfold EAGER0, CBMAX, K_FREEARR_OFF, K_FREEARR_MAX, K_CHUNKS_BLOCK in *. lia.
  - apply (vm_gap_available_intro_N _ _ (LEN0 + LEN0 + (SMAX + 2^15 + 1)) (2^23 + 2^12) (RTOT0 + TOT0 + 2^37)); [lia| | | |].
    + rewrite T3. unfold ACEIL in T1. rewrite CEIL_val. exact T1.
    + eapply Z.le_trans. { apply inj_le. apply length_filter_le. }
      rewrite length_app, Nat2Z.inj_add. fold (zlen (vm_reserved (m_vmmaps mo))). fold (zlen (vm_maps (m_vmmaps mo))).
      unfold zlen at 2. rewrite (Permutation_length HP). fold (zlen (L0 ++ map went (CHX pc pb st))). rewrite zlen_app.
      unfold zlen at 3. rewrite length_map. fold (zlen (CHX pc pb st)). destruct HS as (_ & _ & _ & _ & _ & _ & _ & HL & _). lia.
    + rewrite live_bytes_app'. rewrite (live_bytes_perm' _ _ HP).
      rewrite live_bytes_app', (live_bytes_went _ (CHX_wf _ _ _ HA)). destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HT & _). lia.
    + rewrite CEIL_val, FLOOR_val. unfold LEN0, RTOT0, TOT0, SMAX. lia.
Qed.

Lemma INV_gap_sec : forall st mo n,
  INV [] [] st mo -> 64512 < n <= 2^28 ->
  secbytes (live_chunks st) <= 2^30 -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX ->
  zsum2 (CHX [] [] st) <= 2^37 ->
  vm_gap_available (m_vmmaps mo) (sec_map_size n) = true.
Proof.
  intros st mo n HI Hn HLB Hq1 Hq2 HSB.
  pose proof HI as [HA HM]. pose proof (AMI_ivs_wf _ _ _ HM) as Hwf.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & [[T1 T2] T3] & L0 & HP & HS & HB & HLZ).
  pose proof (sec_map_size_bounds n ltac:(lia)) as SB.

  assert (HCL : zlen (CHX [] [] st) <= 20873).
  { pose proof HA as (HC & HW & HBW & Hb1 & Hb2 & _).
    unfold CHX, CH, all_chunks in *. cbn [app] in *. rewrite !zlen_app. rewrite secs_app, zlen_app.
    apply Forall_app in HW as [HWl HWq].
    destruct (secs_bounds _ HWl) as (A1 & _ & _). destruct (secs_bounds _ HWq) as (B1 & _ & _).
    pose proof (qchunks_secbytes _ HBW) as QS.
    assert (HQB : bsum (qbatches [] st) <= 2^28 + 2^22) by (unfold qbatches; cbn [app]; rewrite bsum_app; unfold Q_CACHE, Q_MAX in *; lia).
    assert (EL : zlen (emb_ent st) <= 1) by (unfold emb_ent; destruct (a_emb st) as [[d cap] sz]; destruct (cap =? 0); unfold zlen; cbn; lia).
    unfold qbatches in *. cbn [app] in *. nia. }
  apply (vm_gap_available_intro_N _ _ (LEN0 + LEN0 + 20873) (2^28 + 2^14) (RTOT0 + TOT0 + 2^37)); [lia| | | |].
  - rewrite T3. unfold ACEIL in T1. rewrite CEIL_val. exact T1.
  - eapply Z.le_trans. { apply inj_le. apply length_filter_le. }
    rewrite length_app, Nat2Z.inj_add. fold (zlen (vm_reserved (m_vmmaps mo))). fold (zlen (vm_maps (m_vmmaps mo))).
    unfold zlen at 2. rewrite (Permutation_length HP). fold (zlen (L0 ++ map went (CHX [] [] st))). rewrite zlen_app.
    unfold zlen at 3. rewrite length_map. fold (zlen (CHX [] [] st)). destruct HS as (_ & _ & _ & _ & _ & _ & _ & HL & _). lia.
  - rewrite live_bytes_app'. rewrite (live_bytes_perm' _ _ HP).
    rewrite live_bytes_app', (live_bytes_went _ (CHX_wf _ _ _ HA)). destruct HS as (_ & _ & _ & _ & _ & _ & _ & _ & HT & _). lia.
  - rewrite CEIL_val, FLOOR_val. unfold LEN0, RTOT0, TOT0. lia.
Qed.

Lemma INV_prim : forall pc pb st mo, INV pc pb st mo ->
  exists pb0, In (went (pb0, PRIM_SZ)) (vm_maps (m_vmmaps mo)) /\ pb0 <= a_space_beg st /\ a_space_beg st + 2^37 + 2^12 <= pb0 + PRIM_SZ
              /\ KHIGH <= pb0 /\ pb0 + PRIM_SZ <= ATOP.
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as ((pb0 & Hin & H1 & H2 & H3 & H4) & _). exists pb0. split; [|repeat split; assumption].
  eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hin.
Qed.

Lemma INV_ptr : forall pc pb st mo, INV pc pb st mo ->
  In (went (a_ptr_array st, PTR_SZ)) (vm_maps (m_vmmaps mo)) /\ a_ptr_array st + PTR_SZ <= ATOP
  /\ region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 (a_ptr_array st)) (Z_to_bv 64 PTR_SZ) = true.
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as (_ & Hin & H1 & H2 & _). split; [|split; assumption].
  eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. left. exact Hin.
Qed.
Lemma INV_shadows : forall pc pb st mo, INV pc pb st mo ->
  In (went (LS_LO, LS_SZ)) (vm_maps (m_vmmaps mo)) /\ In (went (GAP_LO, GAP_SZ)) (vm_maps (m_vmmaps mo)) /\ In (went (HS_LO, HS_SZ)) (vm_maps (m_vmmaps mo)).
Proof.
  intros pc pb st mo [_ HM]. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L0 & HP & HS & _).
  destruct HS as (_ & _ & _ & _ & H1 & H2 & H3 & _).
  repeat split; (eapply Permutation_in; [apply Permutation_sym; exact HP|]; apply in_app_iff; left; assumption).
Qed.

Lemma AINV_geom : forall pc pb st, AINV pc pb st -> a_space_beg st mod 65536 = 0 /\ 0 < a_space_beg st /\ a_ptr_array st mod 4096 = 0 /\ 0 < a_ptr_array st.
Proof. intros pc pb st H. destruct H as (_ & _ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & G4 & _). auto. Qed.

Lemma rup_mod : forall x a, 0 < a -> rup x a mod a = 0.
Proof. intros. unfold rup. apply Z_mod_mult. Qed.
Lemma rup_ge' : forall x a, 0 < a -> x <= rup x a. Proof. exact rup_ge. Qed.

Lemma is_err_small : forall a, 0 <= a <= TWO64 - 4096 -> is_err a = false.
Proof. intros. unfold is_err. apply Z.ltb_ge. lia. Qed.

Lemma mod0_divide : forall x m, 0 < m -> x mod m = 0 -> (m | x).
Proof. intros. apply Z.mod_divide; lia. Qed.
Lemma divide_mod0 : forall x m, 0 < m -> (m | x) -> x mod m = 0.
Proof. intros. apply Z.mod_divide; [lia| assumption]. Qed.
Lemma div4096_of_mod : forall x m, (4096 | m) -> 0 < m -> x mod m = 0 -> (4096 | x).
Proof. intros x m Hm Hp Hx. eapply Z.divide_trans; [exact Hm|]. apply mod0_divide; assumption. Qed.
Lemma div_65536 : (4096 | 65536). Proof. exists 16. reflexivity. Qed.
Lemma div_262144 : (4096 | 262144). Proof. exists 64. reflexivity. Qed.
Lemma div_lit : forall k, (4096 | k * 4096). Proof. intros. exists k. reflexivity. Qed.

Lemma ensure_ok : forall R (P : R -> Model -> Prop) pc pb st c nf (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 1 <= c <= 31 -> 0 <= nf ->
  4 * nf + K_FREEARR_MAP <= K_FREEARR_MAX ->
  zsum2 (CHX pc pb st) <= 2^37 ->
  (forall st' mo', INV pc pb st' mo' -> same_but c st st' ->
     c_mapped_user (get_cls st' c) = c_mapped_user (get_cls st c) ->
     c_allocated_user (get_cls st' c) = c_allocated_user (get_cls st c) ->
     c_num_freed (get_cls st' c) = c_num_freed (get_cls st c) ->
     c_count (get_cls st' c) = c_count (get_cls st c) ->
     nf * 4 <= c_mapped_free_array (get_cls st' c) ->
     atot (k st' true) mo' P) ->
  atot (ensure_free_array st c nf k) mo P.
Proof.
  intros R P pc pb st c nf k mo HI Hc Hnf Hroom HSB Hk.
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as HC.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  destruct (AINV_geom _ _ _ HA) as (G1 & G2 & G3 & G4).
  destruct (INV_prim _ _ _ _ HI) as (pb0 & HinP & P1 & P2 & P3 & P4).
  unfold ensure_free_array. cbv zeta.
  destruct (Z.leb_spec (nf * 4) (c_mapped_free_array (get_cls st c))) as [Hle|Hgt].
  { apply (Hk st mo HI (same_but_refl c st)); auto. }
  pose proof (rup_ge (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R1.
  pose proof (rup_le (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R2.
  pose proof (rup_mod (nf * 4) K_FREEARR_MAP ltac:(unfold K_FREEARR_MAP; lia)) as R3.
  destruct (Z.ltb_spec K_FREEARR_MAX (rup (nf * 4) K_FREEARR_MAP)) as [Hbig|Hok]; [lia|].
  set (len := rup (nf * 4) K_FREEARR_MAP - c_mapped_free_array (get_cls st c)).
  set (a := region_beg st c + K_FREEARR_OFF + c_mapped_free_array (get_cls st c)).
  assert (Hlen : 0 < len <= 2^30) by (unfold len, K_FREEARR_MAX in *; lia).
  assert (Dmfa : (4096 | c_mapped_free_array (get_cls st c))) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_FREEARR_MAP in C7; exact C7]).
  assert (Drup : (4096 | rup (nf * 4) K_FREEARR_MAP)) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_FREEARR_MAP in *; exact R3]).
  assert (Dsb : (4096 | a_space_beg st)) by (apply (div4096_of_mod _ 65536); [apply div_65536| lia| exact G1]).
  assert (Hlm : len mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold len. apply Z.divide_sub_r; assumption. }
  assert (Ham : a mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold a, region_beg, K_REGION, K_FREEARR_OFF.
    apply Z.divide_add_r; [|exact Dmfa]. apply Z.divide_add_r; [| exists 917504; reflexivity].
    apply Z.divide_add_r; [exact Dsb|]. replace (c * 2 ^ 32) with ((c * 2^20) * 4096) by lia. apply div_lit. }
  assert (Hc32 : 0 <= c * 2^32 <= 31 * 2^32) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  assert (HE1 : pb0 <= a) by (unfold a, region_beg, K_REGION, K_FREEARR_OFF; lia).
  assert (HE2 : a + len <= pb0 + PRIM_SZ).
  { unfold a, len, region_beg, K_REGION, K_FREEARR_OFF, K_FREEARR_MAX, PRIM_SZ in *. lia. }
  assert (HBS : B (went (pb0, PRIM_SZ)) = pb0 /\ S (went (pb0, PRIM_SZ)) = PRIM_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PRIM_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  unfold ev. apply atotal_vis.
  - apply (INV_fixed_aok_high pc pb st mo (went (pb0, PRIM_SZ))); auto; try lia. unfold RES_HI, KHIGH in *. lia.
  - intros z mo' Hpost. cbn [apost] in Hpost.
    assert (Hanz : (a =? 0) = false) by (apply Z.eqb_neq; unfold KHIGH in *; lia).
    rewrite Hanz in Hpost. destruct Hpost as [-> ->].
    rewrite fixed_answer_ok_self. cbn [negb].
    rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PRIM_SZ in *; lia).
    assert (ML : mmap_len len = len) by (apply mmap_len_id; lia). rewrite ML.
    apply Hk.
    + split.
      * apply AINV_put_cls; [exact HA| exact Hc|]. unfold CLSOK. cbn [c_allocated_user c_mapped_user c_mapped_free_array c_num_freed c_count cls_set_mapped_free_array].
        unfold K_FREEARR_MAP in *. repeat split; try lia.
      * rewrite ?CHX_put, ?CH_put. apply (AMI_commit _ st _ _ (went (pb0, PRIM_SZ))); auto; try lia; try reflexivity.
        -- rewrite commit_bytes_put by exact Hc. unfold cls_mapped_bytes'. cbn [c_mapped_user c_mapped_free_array cls_set_mapped_free_array]. unfold len. lia.
        -- intros x Hx. left. apply (committed_user_put_grow st c _ x 0) in Hx; [destruct Hx as [X|X]; [exact X| lia]| cbn [c_mapped_user cls_set_mapped_free_array]; lia].
    + apply same_but_put.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. reflexivity.
    + rewrite get_put_eq. cbn [c_mapped_free_array cls_set_mapped_free_array]. lia.
Qed.

Local Ltac cproj := cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count
                         cls_set_allocated_user cls_set_num_freed cls_set_mapped_free_array cls_set_mapped_user cls_set_count negb].

Local Ltac mu_put := apply mu_put_le; cproj; lia.

Lemma populate_g_ok : forall R (P : R -> Model -> Prop) (exh : astate -> (astate -> AM R) -> AM R) (clr : astate -> astate) pc pb st c req (k : astate -> bool -> AM R) mo,
  (forall s, clr s = s \/ clr s = exh_clear c s) ->
  INV pc pb st mo -> 1 <= c <= 31 -> 32 <= size_of_class c <= 65536 -> 0 < req -> req * size_of_class c <= K_USER_MAP ->
  (K_FREEARR_OFF < c_mapped_user (get_cls st c) + K_USER_MAP -> atot (exh st (fun st' => k st' false)) mo P) ->
  zsum2 (CHX pc pb st) <= 2^37 ->
  (forall st' mo', INV pc pb st' mo' -> same_but c st st' ->
     c_count (get_cls st' c) = c_count (get_cls st c) ->
     c_num_freed (get_cls st c) + req <= c_num_freed (get_cls st' c) ->
     atot (k st' true) mo' P) ->
  atot (populate_free_array_g exh clr st c req k) mo P.
Proof.
  intros R P exh clr pc pb st c req k mo Hclr HI Hc Hsz Hreq Hrs HEXH HSB Hk.
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as HC.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct HC as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  destruct (AINV_geom _ _ _ HA) as (G1 & G2 & G3 & G4).
  destruct (INV_prim _ _ _ _ HI) as (pb0 & HinP & P1 & P2 & P3 & P4).
  remember (size_of_class c) as size eqn:Hsize.

  assert (TAIL : forall st1 mo1,
    INV pc pb st1 mo1 -> same_but c st st1 -> c_count (get_cls st1 c) = c_count (get_cls st c) -> c_num_freed (get_cls st1 c) = c_num_freed (get_cls st c) ->
    c_allocated_user (get_cls st1 c) = c_allocated_user (get_cls st c) ->
    c_allocated_user (get_cls st c) + req * size <= c_mapped_user (get_cls st1 c) -> zsum2 (CHX pc pb st1) <= 2^37 ->
    atot (let r1 := get_cls st1 c in
          let new_cnt := (c_mapped_user r1 - c_allocated_user r1) / size in
          let total_freed := c_num_freed r1 + new_cnt in
          ensure_free_array st1 c total_freed (fun st2 ok =>
            if negb ok then k st2 false else
            k (clr (put_cls c (cls_set_allocated_user (c_allocated_user (get_cls st2 c) + new_cnt * size) (cls_set_num_freed total_freed (get_cls st2 c))) st2)) true)) mo1 P).
  { intros st1 mo1 HI1 HSB1 Hcnt1 Hnf1 Hal1 Hen1 HSB2. cbv zeta.
    pose proof HI1 as [HA1 HM1]. pose proof (AINV_cls _ _ _ _ HA1 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10). rewrite <- Hsize in D10.
    pose proof (carve_facts (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) size ltac:(lia) ltac:(lia)) as (Q0 & Qcv & Qrest).
    pose proof (carve_enough_nomap (c_mapped_user (get_cls st1 c)) (c_allocated_user (get_cls st1 c)) size req ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as Hcarve.
    set (q := (c_mapped_user (get_cls st1 c) - c_allocated_user (get_cls st1 c)) / size) in *. set (cv := q * size) in *.
    assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb st1) + nbatch c (qbatches pb st1)).
    { pose proof (cntP_nonneg c (all_chunks pc pb st1)). unfold nbatch. destruct (c =? K_BATCH_CLASS); [pose proof (zlen_nonneg (qbatches pb st1))|]; lia. }

    assert (Hnf' : 4 * (c_num_freed (get_cls st1 c) + q) + K_FREEARR_MAP <= K_FREEARR_MAX).
    { assert (H1 : size * (c_num_freed (get_cls st1 c) + q) <= c_mapped_user (get_cls st1 c)).
      { rewrite Z.mul_add_distr_l. replace (size * q) with cv by (unfold cv; lia).
        assert (size * c_num_freed (get_cls st1 c) <= c_allocated_user (get_cls st1 c)); [|lia].
        rewrite D10. apply Z.mul_le_mono_nonneg_l; lia. }
      assert (H2 : 32 * (c_num_freed (get_cls st1 c) + q) <= K_FREEARR_OFF).
      { apply Z.le_trans with (size * (c_num_freed (get_cls st1 c) + q)); [apply Z.mul_le_mono_nonneg_r; lia| lia]. }
      unfold K_FREEARR_OFF, K_FREEARR_MAP, K_FREEARR_MAX in *. lia. }
    assert (Hcv : cv = q * size) by reflexivity. clearbody cv q.
    apply (ensure_ok R P pc pb st1 c (c_num_freed (get_cls st1 c) + q) _ mo1 HI1 Hc ltac:(lia) Hnf' HSB2).
    intros st2 mo2 HI2 HSB12 E1 E2 E3 E4 E5. cproj.
    pose proof HI2 as [HA2 HM2].
    assert (AC : all_chunks pc pb st2 = all_chunks pc pb st1 /\ qbatches pb st2 = qbatches pb st1).
    { destruct HSB12 as (_&_&_&_&_&Hl&_&Hq1&_&Hq2&_&_). unfold all_chunks, qbatches, live_chunks. rewrite Hl, Hq1, Hq2. split; reflexivity. }
    destruct AC as [AC1 AC2].
    match goal with |- atot (k (clr ?X) true) _ _ => set (stp := X) end.
    assert (HIp : INV pc pb stp mo2).
    { split.
      + apply AINV_put_cls; [exact HA2| exact Hc|].
        pose proof (AINV_cls _ _ _ _ HA2 Hc) as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
        unfold CLSOK. cproj. rewrite <- Hsize. rewrite AC1, AC2. rewrite E1, E2, E3, E4 in *.
        split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact D5|]. split; [exact F6|]. split; [exact F7|].
        split; [lia|]. split; [exact F9|]. rewrite <- Hsize in F10. rewrite AC1, AC2 in F10. rewrite F10, Hcv. ring.
      + unfold stp. rewrite ?CHX_put, ?CH_put. apply (AMI_mono _ st2); auto; [rewrite commit_bytes_put by exact Hc; unfold cls_mapped_bytes'; cproj; lia| mu_put]. }
    assert (HSp : same_but c st stp) by (eapply same_but_trans; [exact HSB1|]; eapply same_but_trans; [exact HSB12| apply same_but_put]).
    assert (Gp : get_cls stp c = cls_set_allocated_user (c_allocated_user (get_cls st2 c) + cv) (cls_set_num_freed (c_num_freed (get_cls st1 c) + q) (get_cls st2 c)))
      by (unfold stp; apply get_put_eq).
    destruct (Hclr stp) as [EC|EC]; rewrite EC; apply Hk.
    - exact HIp.
    - exact HSp.
    - rewrite Gp. cproj. congruence.
    - rewrite Gp. cproj. lia.
    - unfold exh_clear. apply INV_set_exh. exact HIp.
    - eapply same_but_trans; [exact HSp| apply same_but_set_exh].
    - change (get_cls (exh_clear c ?x) c) with (get_cls x c). rewrite Gp. cproj. congruence.
    - change (get_cls (exh_clear c ?x) c) with (get_cls x c). rewrite Gp. cproj. lia. }
  unfold populate_free_array_g. rewrite <- Hsize. cbv zeta.
  destruct (Z.leb_spec (c_allocated_user (get_cls st c) + req * size) (c_mapped_user (get_cls st c))) as [Hen|Hmap].
  { apply (TAIL st mo HI (same_but_refl c st)); auto. }

  assert (Hums : rup (c_allocated_user (get_cls st c) + req * size - c_mapped_user (get_cls st c)) K_USER_MAP = K_USER_MAP).
  { apply rup_small; unfold K_USER_MAP in *; lia. }
  rewrite Hums.
  destruct (Z.ltb_spec K_FREEARR_OFF (c_mapped_user (get_cls st c) + K_USER_MAP)) as [Hex|Hok]; [exact (HEXH Hex)|].
  set (a := region_beg st c + c_mapped_user (get_cls st c)).
  assert (Hc32 : 0 <= c * 2^32 <= 31 * 2^32) by (split; [apply Z.mul_nonneg_nonneg; lia | apply Z.mul_le_mono_nonneg_r; lia]).
  assert (Dsb : (4096 | a_space_beg st)) by (apply (div4096_of_mod _ 65536); [apply div_65536| lia| exact G1]).
  assert (Dmu : (4096 | c_mapped_user (get_cls st c))) by (apply (div4096_of_mod _ 262144); [apply div_262144| lia| unfold K_USER_MAP in C5; exact C5]).
  assert (Ham : a mod 4096 = 0).
  { apply divide_mod0; [lia|]. unfold a, region_beg, K_REGION. apply Z.divide_add_r; [|exact Dmu]. apply Z.divide_add_r; [exact Dsb|].
    replace (c * 2 ^ 32) with ((c * 2^20) * 4096) by lia. apply div_lit. }
  assert (HE1 : pb0 <= a) by (unfold a, region_beg, K_REGION; lia).
  assert (HE2 : a + K_USER_MAP <= pb0 + PRIM_SZ) by (unfold a, region_beg, K_REGION, K_FREEARR_OFF, K_USER_MAP, PRIM_SZ in *; lia).
  assert (HBS : B (went (pb0, PRIM_SZ)) = pb0 /\ S (went (pb0, PRIM_SZ)) = PRIM_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PRIM_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  unfold ev. apply atotal_vis.
  - apply (INV_fixed_aok_high pc pb st mo (went (pb0, PRIM_SZ))); auto; try lia; [unfold RES_HI, KHIGH in *; lia| unfold K_USER_MAP; lia].
  - intros z mo' Hpost. cbn [apost] in Hpost.
    assert (Hanz : (a =? 0) = false) by (apply Z.eqb_neq; unfold KHIGH in *; lia).
    rewrite Hanz in Hpost. destruct Hpost as [-> ->].
    rewrite fixed_answer_ok_self. cbn [negb].
    rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PRIM_SZ, K_USER_MAP in *; lia).
    assert (ML : mmap_len K_USER_MAP = K_USER_MAP) by reflexivity. rewrite ML.
    set (st1 := put_cls c (cls_set_mapped_user (c_mapped_user (get_cls st c) + K_USER_MAP) (get_cls st c)) st).
    assert (HI1 : INV pc pb st1 (fixed_model mo F_FIXED a K_USER_MAP)).
    { split.
      + apply AINV_put_cls; [exact HA| exact Hc|]. unfold CLSOK. cproj. rewrite <- Hsize. repeat split; try (unfold K_USER_MAP in *; lia).
        all: unfold K_USER_MAP in *; rewrite <- Zplus_mod_idemp_l, C5; reflexivity.
      + unfold st1. rewrite ?CHX_put, ?CH_put. apply (AMI_commit _ st _ _ (went (pb0, PRIM_SZ))); auto; try lia; try reflexivity.
        all: try (unfold K_USER_MAP; lia).
        * rewrite commit_bytes_put by exact Hc; unfold cls_mapped_bytes'; cproj; unfold K_USER_MAP; lia.
        *
          intros x Hx. apply (committed_user_put_grow st c _ x K_USER_MAP) in Hx; [fold a in Hx; exact Hx| cproj; lia]. }
    assert (Er1 : get_cls st1 c = cls_set_mapped_user (c_mapped_user (get_cls st c) + K_USER_MAP) (get_cls st c)) by (unfold st1; apply get_put_eq).
    apply (TAIL st1 (fixed_model mo F_FIXED a K_USER_MAP) HI1); try (rewrite Er1; cproj; lia).
    + unfold st1. apply same_but_put.
    + unfold st1. rewrite ?CHX_put, ?CH_put. exact HSB.
Qed.

Lemma populate_ok : forall R (P : R -> Model -> Prop) pc pb st c req (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 1 <= c <= 31 -> 32 <= size_of_class c <= 65536 -> 0 < req -> req * size_of_class c <= K_USER_MAP ->
  c_allocated_user (get_cls st c) + 2^20 <= K_FREEARR_OFF ->
  zsum2 (CHX pc pb st) <= 2^37 ->
  (forall st' mo', INV pc pb st' mo' -> same_but c st st' ->
     c_count (get_cls st' c) = c_count (get_cls st c) ->
     c_num_freed (get_cls st c) + req <= c_num_freed (get_cls st' c) ->
     atot (k st' true) mo' P) ->
  atot (populate_free_array st c req k) mo P.
Proof.
  intros R P pc pb st c req k mo HI Hc Hsz Hreq Hrs Hroom HSB Hk. unfold populate_free_array.
  apply (populate_g_ok R P _ _ pc pb st c req k mo (fun s => or_introl eq_refl) HI Hc Hsz Hreq Hrs); [| exact HSB| exact Hk].
  intros Hex. exfalso. pose proof HI as [HA _]. pose proof (AINV_cls _ _ _ _ HA Hc) as (C1 & C2 & C3 & C4 & _).
  unfold K_USER_MAP, K_FREEARR_OFF in *. lia.
Qed.

Lemma max_count_same_but : forall c st1 st2 c', same_but c st1 st2 -> max_count st2 c' = max_count st1 c'.
Proof. intros c st1 st2 c' H. destruct H as (_&_&_&_&Hci&_). unfold max_count. rewrite Hci. reflexivity. Qed.

Lemma all_chunks_cons : forall ch pc pb st, all_chunks (ch :: pc) pb st = ch :: all_chunks pc pb st. Proof. reflexivity. Qed.
Lemma qbatches_cons : forall b pb st, qbatches (b :: pb) st = b :: qbatches pb st. Proof. reflexivity. Qed.
Lemma CH_cons : forall ch pc pb st, CH (ch :: pc) pb st = sec_of ch ++ CH pc pb st. Proof. reflexivity. Qed.

Lemma CH_repc : forall pc pc' pb st, secs pc' = secs pc -> CH pc' pb st = CH pc pb st.
Proof. intros. unfold CH, all_chunks. rewrite !secs_app, H. reflexivity. Qed.

Lemma AINV_repc : forall pc pc' pb st c r',
  AINV pc pb st -> 1 <= c <= 31 ->
  Forall chunk_wf pc' ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> cntP c' pc' = cntP c' pc) -> secs pc' = secs pc ->
  CLSOK pc' pb st c r' -> AINV pc' pb (put_cls c r' st).
Proof.
  intros pc pc' pb st c r' H Hc Hwf Hcnt Hsec HR. unfold AINV in *.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array put_cls set_cls] in *.
  rewrite (CH_put pc' pb c r' st), (CH_repc pc pc' pb st Hsec).
  split.
  { intros c' Hc'. unfold cls_inv. rewrite max_count_put, all_chunks_put, qbatches_put.
    destruct (Z.eq_dec c' c) as [->|Hne].
    - rewrite get_put_eq. exact HR.
    - rewrite get_put_ne by congruence. pose proof (HC c' Hc') as X. unfold cls_inv in X.
      unfold all_chunks in *. rewrite !cntP_app in *. rewrite (Hcnt c' Hc' Hne). exact X. }
  split.
  { rewrite all_chunks_put. unfold all_chunks in *. apply Forall_app in H2 as [_ H2]. apply Forall_app. split; assumption. }
  rewrite qbatches_put. repeat (split; [assumption|]). assumption.
Qed.

Lemma INV_repc : forall pc pc' pb st c r' mo,
  INV pc pb st mo -> 1 <= c <= 31 ->
  Forall chunk_wf pc' ->
  (forall c', 1 <= c' <= 31 -> c' <> c -> cntP c' pc' = cntP c' pc) -> secs pc' = secs pc ->
  CLSOK pc' pb st c r' -> cls_mapped_bytes' (get_cls st c) <= cls_mapped_bytes' r' ->
  c_mapped_user r' <= c_mapped_user (get_cls st c) ->
  INV pc' pb (put_cls c r' st) mo.
Proof.
  intros pc pc' pb st c r' mo [HA HM] Hc Hwf Hcnt Hsec HR Hmono Hmu. split.
  - apply AINV_repc with (pc := pc); assumption.
  - rewrite ?CHX_put; unfold CHX; rewrite ?CH_put, (CH_repc pc pc' pb st Hsec). apply (AMI_mono _ st); auto; [rewrite commit_bytes_put by exact Hc; lia| apply mu_put_le; exact Hmu].
Qed.

Lemma AINV_init_cache : forall pc pb st, AINV pc pb st -> AINV pc pb (init_cache st).
Proof.
  intros pc pb st H. unfold init_cache. destruct (a_cinit st) eqn:E; [exact H|].
  unfold AINV in *. destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_cinit a_cinit] in *.
  split; [| repeat (split; [assumption|]); assumption].
  intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold max_count in *. cbn [a_cinit set_cinit] in *. rewrite E in X.
  unfold get_cls in *. cbn [a_cls set_cinit] in *.
  unfold all_chunks, qbatches, live_chunks in *. cbn [a_live a_qloc a_qglob set_cinit] in *.
  pose proof (primary_class_facts 0 ltac:(lia) eq_refl) as _.
  assert (0 <= max_cached c) by (unfold max_cached; lia). lia.
Qed.

Lemma INV_init_cache : forall pc pb st mo, INV pc pb st mo -> INV pc pb (init_cache st) mo.
Proof.
  intros pc pb st mo [HA HM]. split; [apply AINV_init_cache; exact HA|].
  rewrite ?CHX_init_cache, ?CH_init_cache. apply (AMI_mono _ st); auto.
  - unfold init_cache; destruct (a_cinit st); reflexivity.
  - unfold init_cache; destruct (a_cinit st); reflexivity.
  - rewrite commit_bytes_init_cache. lia.
  - intros c0 _. rewrite get_cls_init_cache. lia.
Qed.

Lemma same_but_init_cache : forall c st, same_but c (init_cache st) st \/ True. Proof. intros. right. exact I. Qed.

Lemma AMI_perm : forall ch ch' st mo, Permutation ch ch' -> AMI ch st mo -> AMI ch' st mo.
Proof.
  intros ch ch' st mo HP H. destruct H as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HPm & HS & HB & HLZ).
  unfold AsanInv.AMI. repeat (split; [assumption|]). exists L0. split; [|split; [assumption| split; assumption]].
  eapply Permutation_trans; [exact HPm|]. apply Permutation_app_head. apply Permutation_map. exact HP.
Qed.

Lemma AINV_live_perm : forall pc pc' pb st lv nx,
  AINV pc pb st ->
  Permutation (all_chunks pc' pb (set_next nx (set_live lv st))) (all_chunks pc pb st) ->
  (forall id ch, lv !! id = Some ch -> (id < nx)%N) ->
  live_budget (set_next nx (set_live lv st)) ->
  AINV pc' pb (set_next nx (set_live lv st)).
Proof.
  intros pc pc' pb st lv nx H HP Hid HLB. unfold AINV in *.
  destruct H as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13).
  cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_next set_live a_cinit] in *.
  assert (Hq : qbatches pb (set_next nx (set_live lv st)) = qbatches pb st) by reflexivity.
  assert (HCH : zlen (CH pc' pb (set_next nx (set_live lv st))) = zlen (CH pc pb st)).
  { unfold CH, zlen. f_equal. apply Permutation_length. apply secs_perm. exact HP. }
  split.
  { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_next set_live] in *.
    rewrite Hq, (cntP_perm c _ _ HP). exact X. }
  split. { eapply Permutation_Forall; [apply Permutation_sym; exact HP| exact H2]. }
  rewrite Hq, HCH. repeat (split; [assumption|]). exact (proj2 H13).
Qed.

Lemma INV_hand_to_live : forall ch pc pb st mo,
  INV (ch :: pc) pb st mo ->
  live_budget_list (ch :: live_chunks st) ->
  INV pc pb (set_next (N.succ (a_next st)) (set_live (<[a_next st := ch]> (a_live st)) st)) mo.
Proof.
  intros ch pc pb st mo [HA HM] HLB.
  assert (Hnone : (a_live st) !! (a_next st) = None).
  { destruct ((a_live st) !! (a_next st)) as [ch0|] eqn:E; [|reflexivity]. exfalso.
    destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ E). lia. }
  pose proof (live_chunks_insert st (a_next st) ch Hnone) as HPl.
  assert (HP : Permutation (all_chunks pc pb (set_next (N.succ (a_next st)) (set_live (<[a_next st := ch]> (a_live st)) st))) (all_chunks (ch :: pc) pb st)).
  { unfold all_chunks. cbn [app]. unfold live_chunks in *. cbn [a_live set_next set_live] in *.
    change (qbatches pb (set_next (N.succ (a_next st)) (set_live (<[a_next st:=ch]> (a_live st)) st))) with (qbatches pb st).
    eapply Permutation_trans. { apply Permutation_app_head. apply Permutation_app_tail. exact HPl. }
    rewrite app_comm_cons. apply Permutation_sym. cbn. apply Permutation_middle. }
  split.
  - apply (AINV_live_perm (ch :: pc)); auto.
    + intros id ch0 Hl. destruct (N.eq_dec id (a_next st)) as [->|Hne]; [lia|].
      rewrite lookup_insert_ne in Hl by congruence. destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ Hl). lia.
    + apply live_budget_list_iff. unfold live_chunks. cbn [a_live set_next set_live]. unfold live_chunks in HPl. cbn [a_live set_live] in HPl.
      destruct HLB as (B1 & B2 & B3). split; [|split].
      * rewrite (cntP_perm K_BATCH_CLASS _ _ HPl). exact B1.
      * unfold zlen in *. rewrite (Permutation_length (secs_perm _ _ HPl)). exact B2.
      * assert (E : forall l l', Permutation l l' -> secbytes l = secbytes l').
        { intros l l' P0. induction P0; cbn; try lia. - destruct x; lia. - destruct x, y; lia. }
        rewrite (E _ _ HPl). exact B3.
  - apply (AMI_perm (CHX (ch :: pc) pb st)).
    + unfold CHX. apply Permutation_app_tail. unfold CH. apply secs_perm. apply Permutation_sym. exact HP.
    + apply (AMI_mono _ st); auto; [apply Z.le_refl || (unfold commit_bytes, csum, get_cls; cbn; lia)| intros c0 _; apply Z.le_refl].
Qed.

Lemma rdn_le : forall x a, 0 < a -> rdn x a <= x. Proof. intros. unfold rdn. rewrite Z.mul_comm. apply Z.mul_div_le. lia. Qed.
Lemma rdn_mod : forall x a, 0 < a -> rdn x a mod a = 0. Proof. intros. unfold rdn. apply Z_mod_mult. Qed.

Lemma poison0_ok : forall R (P : R -> Model -> Prop) pc pb st (k : AM R) mo a s,
  INV pc pb st mo -> 0 <= a -> 0 <= s <= 2^32 - 2^20 ->
  (a + s <= LS_LO \/ (KHIGH <= a /\ a + s <= ATOP)) ->
  zsum2 (CHX pc pb st) <= 2^37 ->
  (forall mo', INV pc pb st mo' -> atot k mo' P) ->
  atot (poison0 a s k) mo P.
Proof.

  intros R P pc pb st k mo a s HI Ha Hs Hrange HSB Hk. unfold poison0. apply Hk. exact HI.
Qed.

Lemma grant_range : forall pc pb st mo z n,
  INV pc pb st mo -> 0 < z -> 0 < n -> z + n <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 n) = true ->
  z + n <= LS_LO \/ (KHIGH <= z /\ z + n <= ATOP).
Proof.
  intros pc pb st mo z n HI Hz Hn Hce Hrf.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct (INV_shadows _ _ _ _ HI) as (HinLS & HinGAP & HinHS).
  rewrite region_free_app in Hrf. apply andb_true_iff in Hrf as [_ Hrf].
  pose proof (region_free_wsep _ _ _ Hrf) as HW. rewrite Forall_forall in HW.
  pose proof (HW _ HinLS) as W1. pose proof (HW _ HinGAP) as W2. pose proof (HW _ HinHS) as W3.
  unfold wsep, went in W1, W2, W3. cbn [fst snd] in W1, W2, W3.
  unfold ACEIL, LS_LO, LS_SZ, GAP_LO, GAP_SZ, HS_LO, HS_SZ, KHIGH in *. rewrite !unsigned_lit in W1, W2, W3 by lia. lia.
Qed.

Lemma filter_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> Permutation (List.filter f l) (List.filter f l').
Proof.
  intros A f l l' HP. induction HP as [|x l l' HP IH|x y l|l l' l'' H1 IH1 H2 IH2]; cbn.
  - constructor.
  - destruct (f x); [apply perm_skip|]; exact IH.
  - destruct (f y), (f x); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply Permutation_trans; eassumption.
Qed.
Lemma zsizes_perm : forall l l', Permutation l l' -> zsizes l = zsizes l'.
Proof. intros l l' HP. induction HP; cbn; lia. Qed.
Lemma zsizes_filter_le : forall f l, Forall (fun e => 0 <= snd e) l -> zsizes (List.filter f l) <= zsizes l.
Proof. induction l as [|e l IH]; intros HF; cbn; [lia|]. apply Forall_cons_iff in HF as [He HF]. specialize (IH HF). destruct (f e); cbn; lia. Qed.
Lemma filter_none : forall {A} (f : A -> bool) l, Forall (fun x => f x = false) l -> List.filter f l = [].
Proof. induction l as [|x l IH]; intros HF; cbn; [reflexivity|]. apply Forall_cons_iff in HF as [Hx HF]. rewrite Hx. apply IH. exact HF. Qed.
Lemma zsizes_zent_went : forall ch, Forall (fun e => 0 <= snd e < 2^64) ch -> Forall (fun e => 0 <= fst e < 2^64) ch ->
  zsizes (map zent (map went ch)) = zsum2 ch.
Proof.
  induction ch as [|[mb ms] ch IH]; intros H1 H2; cbn -[Z_to_bv bv_unsigned Z.pow]; [reflexivity|].
  apply Forall_cons_iff in H1 as [A1 H1]. apply Forall_cons_iff in H2 as [A2 H2]. cbn [fst snd] in A1, A2.
  rewrite unsigned_lit by lia. rewrite (IH H1 H2). reflexivity.
Qed.

Lemma achunks_all_chunks : forall pc pb st ch, In ch (achunks st) -> In ch (all_chunks pc pb st).
Proof.
  intros pc pb st ch Hin. unfold achunks, all_chunks, live_chunks, qchunks, qbatches in *.
  apply in_app_iff. right. apply in_app_iff in Hin as [Hin|Hin]; apply in_app_iff; [left; exact Hin| right].
  apply in_flat_map in Hin as (b & Hb & Hin). apply in_flat_map. exists b. split; [|exact Hin]. apply in_app_iff. right. exact Hb.
Qed.

Lemma grant_avoids : forall pc pb st mo z len,
  INV pc pb st mo -> 0 < z -> 0 < len -> z + len <= ATOP ->
  region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 z) (Z_to_bv 64 len) = true ->
  avoids_all z len (RESV ++ asec_ranges st) = true.
Proof.
  intros pc pb st mo z len HI Hz Hlen Hce Hrf.
  pose proof HI as [HA HM]. pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HPm & HS & HB & HLZ).
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRC).
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  assert (ZL : 0 <= z < 2^64 /\ 0 <= len < 2^64) by lia.
  assert (RF : forall e, In e (vm_reserved (m_vmmaps mo) ++ L0 ++ map went (CHX pc pb st)) ->
               z + len <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= z).
  { intros [b sz] He. pose proof (region_free_In _ _ _ b sz Hrf) as X. rewrite !unsigned_lit in X by lia. cbn [fst snd]. apply X.
    apply in_app_iff in He as [He|He]; apply in_app_iff; [left; exact He| right].
    eapply Permutation_in; [apply Permutation_sym; exact HPm| exact He]. }
  unfold avoids_all. apply forallb_forall. intros [lo hi] Hin. unfold iv_clear. cbn [fst snd].
  apply in_app_iff in Hin as [Hin|Hin].
  -
    destruct (proj1 (Forall_forall _ _) HRC _ Hin) as (e & He & C1 & C2). cbn [fst snd] in C1, C2.
    specialize (RF e ltac:(rewrite app_assoc; apply in_app_iff; left; exact He)).
    apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia.
  -
    unfold asec_ranges in Hin. apply in_app_iff in Hin as [Hin|Hin].
    2:{ destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE). unfold emb_ok in HE. unfold emb_iv in Hin.
        assert (HinX : forall d cap, a_emb st = (d, cap, snd (a_emb st)) -> cap <> 0 -> In (d, cap) (CHX pc pb st)).
        { intros d cap E NZ. unfold CHX, emb_ent. apply in_app_iff. right. rewrite E. destruct (Z.eqb_spec cap 0); [contradiction| left; reflexivity]. }
        destruct (a_emb st) as [[d cap] sz] eqn:EE. destruct (Z.eqb_spec cap 0) as [|NZ]; [destruct Hin|]. destruct Hin as [E|[]]. injection E as <- <-.
        destruct HE as [[E0 _]|(E1 & E2 & E3 & E4 & E5 & E6)]; [contradiction|]. unfold EMB_INIT, EMB_MAX, LS_LO, KHIGH in *.
        specialize (RF (went (d, cap)) ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_map; apply HinX; [reflexivity| exact NZ])).
        unfold went in RF. cbn [fst snd] in RF. rewrite !unsigned_lit in RF by lia.
        apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia. }
    apply in_flat_map in Hin as (ch & Hch & Hin).
    destruct ch as [c n|mb ms n]; cbn in Hin; [destruct Hin|]. destruct Hin as [E|[]]. injection E as <- <-.
    pose proof (achunks_all_chunks pc pb st _ Hch) as Hall.
    assert (HinCH : In (mb, ms) (CH pc pb st)).
    { unfold CH, secs. apply in_flat_map. exists (CSec mb ms n). split; [exact Hall| cbn; left; reflexivity]. }
    destruct HA as (_ & HW & _). pose proof (proj1 (Forall_forall _ _) HW _ Hall) as Hwf. cbn in Hwf.
    destruct Hwf as (Hn' & Hms & Hwf). pose proof (sec_map_size_bounds n ltac:(lia)). unfold LS_LO, KHIGH, ACEIL in Hwf.
    specialize (RF (went (mb, ms)) ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_map; unfold CHX; apply in_app_iff; left; exact HinCH)).
    unfold went in RF. cbn [fst snd] in RF. rewrite !unsigned_lit in RF by lia.
    apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia.
Qed.

Lemma INV_emb_c6 : forall st mo, INV [] [] st mo ->
  let '(d, cap, _) := a_emb st in
  cap <= EMB_MAX
  /\ (cap = 0 \/ avoids_all d cap (RESV ++ flat_map sec_iv (achunks st)) = true)
  /\ (cap = 0 \/ (0 <= d /\ d + cap <= 2^64 /\ forall x, d <= x < d + cap -> covered (m_vm_lazy mo) x = false)).
Proof.
  intros st mo HI.
  pose proof HI as [HA HM]. pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & [M9 M9r] & MT & L0 & HPm & HS & HB & HLZ).
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & HRC).
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  pose proof HA as (_ & HW & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE). unfold emb_ok in HE.
  destruct (a_emb st) as [[d cap] sz] eqn:EE.
  destruct HE as [[-> _]|(E1 & E2 & E3 & E4 & E5 & E6)]; [split; [unfold EMB_MAX; lia| split; left; reflexivity]|].
  unfold EMB_INIT, EMB_MAX, LS_LO, KHIGH in *.
  assert (NZ : cap <> 0) by lia.
  assert (HinX : In (d, cap) (CHX [] [] st)).
  { unfold CHX, emb_ent. apply in_app_iff. right. rewrite EE. destruct (Z.eqb_spec cap 0); [contradiction| left; reflexivity]. }
  assert (DL : 0 <= d /\ d + cap < 2^64) by lia.

  assert (RF : forall e, In e (vm_reserved (m_vmmaps mo) ++ L0 ++ map went (CH [] [] st)) ->
               d + cap <= bv_unsigned (fst e) \/ bv_unsigned (fst e) + bv_unsigned (snd e) <= d).
  { intros e He. apply in_app_iff in He as [He|He].
    -
      pose proof (AMI_ch_entry _ _ _ _ _ HM HinX) as HinM.
      pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) M9r _ HinM) e He) as W.
      unfold went in W. cbn [fst snd] in W. rewrite !unsigned_lit in W by lia. lia.
    -
      assert (HS2 : seps ((L0 ++ map went (CH [] [] st)) ++ [went (d, cap)])).
      { apply (seps_perm (vm_maps (m_vmmaps mo))); [| exact M9].
        eapply Permutation_trans; [exact HPm|]. unfold CHX, emb_ent. rewrite EE. destruct (Z.eqb_spec cap 0); [contradiction|].
        rewrite map_app. cbn [map]. rewrite app_assoc. apply Permutation_refl. }
      pose proof (seps_app_wsep _ _ e (went (d, cap)) HS2 He (or_introl eq_refl)) as W.
      unfold wsep, went in W. cbn [fst snd] in W. rewrite !unsigned_lit in W by lia. lia. }
  split; [lia|]. split.
  - right. unfold avoids_all. apply forallb_forall. intros [lo hi] Hin. unfold iv_clear. cbn [fst snd].
    apply in_app_iff in Hin as [Hin|Hin].
    + destruct (proj1 (Forall_forall _ _) HRC _ Hin) as (e & He & C1 & C2). cbn [fst snd] in C1, C2.
      specialize (RF e ltac:(rewrite app_assoc; apply in_app_iff; left; exact He)).
      apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia.
    + apply in_flat_map in Hin as (ch & Hch & Hin).
      destruct ch as [c n|mb ms n]; cbn in Hin; [destruct Hin|]. destruct Hin as [E|[]]. injection E as <- <-.
      pose proof (achunks_all_chunks [] [] st _ Hch) as Hall.
      assert (HinCH : In (mb, ms) (CH [] [] st)).
      { unfold CH, secs. apply in_flat_map. exists (CSec mb ms n). split; [exact Hall| cbn; left; reflexivity]. }
      pose proof (proj1 (Forall_forall _ _) HW _ Hall) as Hwf. cbn in Hwf.
      destruct Hwf as (Hn' & Hms & Hwf). pose proof (sec_map_size_bounds n ltac:(lia)). unfold LS_LO, KHIGH, ACEIL in Hwf.
      specialize (RF (went (mb, ms)) ltac:(apply in_app_iff; right; apply in_app_iff; right; apply in_map; exact HinCH)).
      unfold went in RF. cbn [fst snd] in RF. rewrite !unsigned_lit in RF by lia.
      apply orb_true_iff. destruct RF as [X|X]; [left| right]; apply Z.leb_le; lia.
  - right. split; [lia|]. split; [lia|]. intros x Hx. apply (AMI_lazy_ch _ _ _ d cap x HM HinX); lia.
Qed.

Definition same_core (st st' : astate) : Prop :=
  a_space_beg st' = a_space_beg st /\ a_ptr_array st' = a_ptr_array st /\ a_nres st' = a_nres st /\ a_nsec st' = a_nsec st
  /\ a_cls st' = a_cls st /\ a_live st' = a_live st /\ a_next st' = a_next st
  /\ a_qloc st' = a_qloc st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob st' = a_qglob st /\ a_qglob_bytes st' = a_qglob_bytes st.

Definition emb_sz (st : astate) : Z := snd (a_emb st).
Lemma same_core_refl : forall st, same_core st st. Proof. intros. unfold same_core. repeat split; reflexivity. Qed.
Lemma same_core_trans : forall a b c, same_core a b -> same_core b c -> same_core a c.
Proof. intros a b c A B. unfold same_core in *. destruct A as (?&?&?&?&?&?&?&?&?&?&?). destruct B as (?&?&?&?&?&?&?&?&?&?&?). repeat split; congruence. Qed.
Lemma same_core_set_emb : forall v st, same_core st (set_emb v st). Proof. intros. unfold same_core. repeat split; reflexivity. Qed.
Lemma same_core_set_exh : forall v st, same_core st (set_exh v st). Proof. intros. unfold same_core. repeat split; reflexivity. Qed.
Lemma CH_same_core : forall pc pb st st', same_core st st' -> CH pc pb st' = CH pc pb st.
Proof. intros pc pb st st' (_&_&_&_&_&Hl&_&Hq1&_&Hq2&_). unfold CH, all_chunks, live_chunks, qbatches. rewrite Hl, Hq1, Hq2. reflexivity. Qed.

Lemma AINV_set_emb : forall pc pb st v, AINV pc pb st -> emb_ok ATOP (set_emb v st) -> AINV pc pb (set_emb v st).
Proof.
  intros pc pb st v H HE. unfold AINV in *.
  destruct H as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9 & H10 & H11 & H12 & H13 & _).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. split; [exact H5|]. split; [exact H6|]. split; [exact H7|].
  split; [exact H8|]. split; [exact H9|]. split; [exact H10|]. split; [exact H11|]. split; [exact H12|]. split; [exact H13| exact HE].
Qed.

Lemma AMI_munmap_aok : forall ch st mo mb ms,
  AMI ch st mo -> In (mb, ms) ch ->
  0 < mb -> mb mod 4096 = 0 -> 0 < ms <= 2^32 -> ms mod 4096 = 0 -> mb + ms <= ATOP ->
  aok (AMunmap mb ms) mo.
Proof.
  intros ch st mo mb ms HM Hin Hmb Hal Hms Hml Hce.
  pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & MT & L0 & HP & HS & HB & HLZ).
  assert (ML : mmap_len ms = ms) by (apply mmap_len_id; lia).
  cbn [AsanNodeSem.aok]. rewrite ML. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  apply map_has_In. eapply Permutation_in; [apply Permutation_sym; exact HP|]. apply in_app_iff. right.
  change (Z_to_bv 64 mb, Z_to_bv 64 ms) with (went (mb, ms)). apply in_map. exact Hin.
Qed.

Lemma rup_PG_id : forall x, 0 <= x -> x mod 4096 = 0 -> rup x PG = x.
Proof.
  intros x Hx Hm. unfold rup, PG. pose proof (Z.div_mod x 4096 ltac:(lia)) as Hd. rewrite Hm in Hd.
  replace (x + 4096 - 1) with (x / 4096 * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095/4096) with 0. lia.
Qed.

Lemma emb_realloc_ok : forall R (P : R -> Model -> Prop) pc pb st want (k : astate -> AM R) mo,
  INV pc pb st mo -> 0 < want -> EMB_INIT <= rup want PG <= EMB_MAX -> emb_sz st <= rup want PG ->
  zsum2 (CH pc pb st) <= 2^37 - 2^24 -> zlen (CH pc pb st) <= SMAX + 2^15 - 1 ->
  (forall mb mo', INV pc pb (set_emb (mb, rup want PG, emb_sz st) st) mo' -> atot (k (set_emb (mb, rup want PG, emb_sz st) st)) mo' P) ->
  atot (emb_realloc ATOP RESV st want k) mo P.
Proof.
  intros R P pc pb st want k mo HI Hw Hcap Hsz HSB HSL Hk.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  pose proof HI as [HA HM].
  pose proof (emb_ent_zsum2 _ _ _ HA) as EZ.
  assert (EL : zlen (emb_ent st) <= 1).
  { unfold emb_ent. destruct (a_emb st) as [[d0 c0] s0]. destruct (c0 =? 0); unfold zlen; cbn; lia. }
  assert (HSBX : zsum2 (CHX pc pb st) <= 2^37 - 2^23) by (rewrite zsum2_CHX; unfold EMB_MAX in EZ; lia).
  assert (HSLX : zlen (CHX pc pb st) <= SMAX + 2^15) by (unfold CHX; rewrite zlen_app; lia).
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE). unfold emb_ok in HE.
  unfold emb_realloc, emb_sz in *. destruct (a_emb st) as [[d cap] sz] eqn:EE. cbn [snd] in *.
  set (ncap := rup want PG) in *.
  assert (NM : ncap mod 4096 = 0) by (unfold ncap; apply (rup_mod want PG); unfold PG; lia).
  unfold EMB_INIT, EMB_MAX in Hcap.
  assert (RUP : rup ncap PG = ncap) by (apply rup_PG_id; lia).
  unfold ev. apply atotal_vis.
  { apply (INV_grant_emb_aok pc pb st mo ncap HI); unfold EMB_MAX; lia. }
  intros z mo' Hpost. cbn [apost] in Hpost. rewrite Z.eqb_refl in Hpost.
  assert (ML : mmap_len ncap = ncap) by (apply mmap_len_id; lia). rewrite ML in Hpost.
  destruct Hpost as (Z1 & Z2 & Z3 & Z4 & ->).
  assert (Hok : mmap_answer_ok ATOP ncap z = true).
  { unfold mmap_answer_ok. rewrite RUP. apply orb_true_iff. right. unfold TWO64, PG.
    rewrite (proj2 (Z.ltb_lt 0 z)) by lia. rewrite Z1. cbn [Z.eqb andb]. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Hok. cbn [negb]. rewrite is_err_small by (unfold TWO64; lia).
  pose proof (grant_range pc pb st mo z ncap HI Z2 ltac:(lia) Z3 Z4) as Hrange.
  pose proof (grant_avoids pc pb st mo z ncap HI Z2 ltac:(lia) Z3 Z4) as HAV.
  rewrite HAV. cbn [andb negb].
  set (st1 := set_emb (z, ncap, sz) st).
  assert (AMI1 : AMI ((z, ncap) :: CHX pc pb st) st (grant_model mo z ncap)) by (apply AMI_grant; auto; lia).
  assert (SZ0 : 0 <= sz) by (destruct HE as [[_ E]|(_ & _ & _ & _ & E & _)]; lia).
  assert (HE1 : emb_ok ATOP st1).
  { unfold emb_ok, st1. cbn [a_emb set_emb]. right. unfold EMB_INIT, EMB_MAX. repeat split; first [lia| exact Hrange]. }
  assert (HA1 : AINV pc pb st1) by (apply AINV_set_emb; assumption).
  assert (NC0 : (ncap =? 0) = false) by (apply Z.eqb_neq; lia).
  assert (CHX1 : CHX pc pb st1 = CH pc pb st ++ [(z, ncap)]).
  { unfold CHX, st1, emb_ent. cbn [a_emb set_emb]. rewrite NC0. reflexivity. }
  destruct (Z.eqb_spec cap 0) as [C0|CN].
  - apply (Hk z). fold st1. split; [exact HA1|]. rewrite CHX1.
    apply (AMI_perm ((z, ncap) :: CH pc pb st)); [apply Permutation_cons_append|].
    assert (CX0 : CHX pc pb st = CH pc pb st) by (unfold CHX, emb_ent; rewrite EE, C0; cbn; apply app_nil_r).
    rewrite CX0 in AMI1. apply (AMI_mono _ st); [exact AMI1| reflexivity| reflexivity| apply Z.le_refl| intros c0 _; apply Z.le_refl].
  - destruct HE as [[E0 _]|(E1 & E2 & E3 & E4 & E5 & E6)]; [contradiction|]. unfold EMB_INIT, EMB_MAX in E1.
    assert (CXN : CHX pc pb st = CH pc pb st ++ [(d, cap)]).
    { unfold CHX, emb_ent. rewrite EE. destruct (Z.eqb_spec cap 0); [contradiction| reflexivity]. }
    assert (DTOP : d + cap <= ATOP) by (unfold LS_LO in E6; destruct E6 as [?|[_ ?]]; lia).
    apply atotal_vis.
    { apply (AMI_munmap_aok ((z, ncap) :: CHX pc pb st) st _ d cap AMI1); try lia.
      right. rewrite CXN. apply in_app_iff. right. left. reflexivity. }
    intros z2 mo2 Hpost2. cbn [apost] in Hpost2. destruct Hpost2 as [-> ->]. rewrite Z.eqb_refl.
    assert (ML2 : mmap_len cap = cap) by (apply mmap_len_id; lia). rewrite ML2.
    apply (Hk z). fold st1. split; [exact HA1|]. rewrite CHX1.
    apply (AMI_perm ((z, ncap) :: CH pc pb st)); [apply Permutation_cons_append|].
    rewrite CXN in AMI1. change ((z, ncap) :: CH pc pb st ++ [(d, cap)]) with (((z, ncap) :: CH pc pb st) ++ (d, cap) :: []) in AMI1.
    pose proof (AMI_munmap ((z, ncap) :: CH pc pb st) [] st st1 _ d cap AMI1 ltac:(lia) ltac:(lia) DTOP eq_refl eq_refl (Z.le_refl _) (fun c0 _ => Z.le_refl _)) as X.
    rewrite app_nil_r in X. exact X.
Qed.

Lemma emb_append_ok : forall R (P : R -> Model -> Prop) pc pb st len (k : astate -> AM R) mo,
  INV pc pb st mo -> 0 < len <= 100 -> emb_sz st + len <= EMB_MAX - 4096 ->
  zsum2 (CH pc pb st) <= 2^37 - 2^24 -> zlen (CH pc pb st) <= SMAX + 2^15 - 1 ->
  (forall st' mo', INV pc pb st' mo' -> same_core st st' -> a_exh st' = a_exh st -> emb_sz st' = emb_sz st + len -> atot (k st') mo' P) ->
  atot (emb_append ATOP RESV st len k) mo P.
Proof.
  intros R P pc pb st len k mo HI Hlen Hroom HSB HSL Hk.

  assert (GO : forall st1 mo1, INV pc pb st1 mo1 -> same_core st st1 -> a_exh st1 = a_exh st -> emb_sz st1 = emb_sz st ->
            (let '(_, cap, _) := a_emb st1 in cap <> 0) ->
            atot (let '(_, cap, sz) := a_emb st1 in
                  let ns := sz + len in
                  if cap <? ns then emb_realloc ATOP RESV st1 ns (fun st2 => k (emb_set_size ns st2)) else k (emb_set_size ns st1)) mo1 P).
  { intros st1 mo1 HI1 SC1 EX1 ES1 CN1. pose proof HI1 as [HA1 HM1].
    pose proof HA1 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE). unfold emb_ok in HE. unfold emb_sz in *.
    destruct (a_emb st1) as [[d1 cap1] sz1] eqn:EE1. cbn [snd] in *. cbv zeta.
    destruct HE as [[E0 _]|(E1 & E2 & E3 & E4 & E5 & E6)]; [contradiction|]. unfold EMB_INIT, EMB_MAX in *.
    assert (FIN : forall st2 mo2, INV pc pb st2 mo2 -> same_core st st2 -> a_exh st2 = a_exh st ->
              (exists d2 cap2, a_emb st2 = (d2, cap2, sz1) /\ sz1 + len <= cap2) ->
              atot (k (emb_set_size (sz1 + len) st2)) mo2 P).
    { intros st2 mo2 [HA2 HM2] SC2 EX2 (d2 & cap2 & EE2 & LE2).
      pose proof HA2 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE2). unfold emb_ok in HE2. rewrite EE2 in HE2.
      destruct HE2 as [[E0 _]|(F1 & F2 & F3 & F4 & F5 & F6)]; [lia|].
      apply Hk.
      - unfold emb_set_size. rewrite EE2. split.
        + apply AINV_set_emb; [exact HA2|]. unfold emb_ok. cbn [a_emb set_emb]. right. repeat split; first [lia| exact F6].
        + assert (CX : CHX pc pb (set_emb (d2, cap2, sz1 + len) st2) = CHX pc pb st2).
          { unfold CHX, emb_ent. cbn [a_emb set_emb]. rewrite EE2. reflexivity. }
          rewrite CX. apply (AMI_mono _ st2); [exact HM2| reflexivity| reflexivity| apply Z.le_refl| intros c0 _; apply Z.le_refl].
      - unfold emb_set_size. rewrite EE2. eapply same_core_trans; [exact SC2| apply same_core_set_emb].
      - unfold emb_set_size. rewrite EE2. exact EX2.
      - unfold emb_set_size. rewrite EE2. cbn [a_emb set_emb snd]. lia. }
    destruct (Z.ltb_spec cap1 (sz1 + len)) as [GROW|FIT].
    - apply (emb_realloc_ok R P pc pb st1 (sz1 + len) _ mo1 HI1); try lia.
      + pose proof (rup_ge (sz1 + len) PG ltac:(unfold PG; lia)). pose proof (rup_le (sz1 + len) PG ltac:(unfold PG; lia)). unfold PG in *. unfold EMB_INIT, EMB_MAX. lia.
      + unfold emb_sz. rewrite EE1. cbn [snd]. pose proof (rup_ge (sz1 + len) PG ltac:(unfold PG; lia)). lia.
      + rewrite (CH_same_core pc pb st st1 SC1). exact HSB.
      + rewrite (CH_same_core pc pb st st1 SC1). exact HSL.
      + intros mb mo' HI'. unfold emb_sz in *. rewrite EE1 in *. cbn [snd] in *.
        apply FIN; [exact HI'| eapply same_core_trans; [exact SC1| apply same_core_set_emb]| exact EX1|].
        exists mb, (rup (sz1 + len) PG). split; [reflexivity|]. apply rup_ge. unfold PG. lia.
    - apply FIN; [exact HI1| exact SC1| exact EX1|]. exists d1, cap1. split; [exact EE1| lia]. }
  unfold emb_append. cbv zeta. pose proof HI as [HA HM].
  pose proof HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HE). unfold emb_ok in HE.
  pose proof (GO st mo HI (same_core_refl st) eq_refl eq_refl) as G0.
  destruct (a_emb st) as [[d0 cap0] sz0] eqn:EE0.
  destruct (Z.eqb_spec cap0 0) as [C0|CN].
  -
    apply (emb_realloc_ok R P pc pb st EMB_INIT _ mo HI); try assumption.
    + unfold EMB_INIT. lia.
    + unfold EMB_INIT, EMB_MAX, rup, PG. cbn. lia.
    + unfold emb_sz. rewrite EE0. cbn [snd]. destruct HE as [[_ E]|(_ & _ & _ & _ & E & _)]; unfold EMB_INIT, rup, PG in *; cbn in *; lia.
    + intros mb mo' HI'. apply (GO _ mo' HI'); [apply same_core_set_emb| reflexivity| reflexivity|].
      cbn [a_emb set_emb]. unfold EMB_INIT, rup, PG. cbn. lia.
  - apply G0. exact CN.
Qed.

Lemma ndigits_range : forall z, 1 <= ndigits z <= 5.
Proof. intros z. unfold ndigits. repeat match goal with |- context [if ?b then _ else _] => destruct b end; lia. Qed.
Lemma exh_len2_bound : forall c, 0 < exh_len2 c <= 70.
Proof. intros c. unfold exh_len2. pose proof (ndigits_range c). pose proof (ndigits_range (size_of_class c)). lia. Qed.

Lemma exh_report_ok : forall R (P : R -> Model -> Prop) pc pb c st (k : astate -> AM R) mo,
  INV pc pb st mo -> 1 <= c <= 31 -> emb_sz st + 110 <= EMB_MAX - 4096 ->
  zsum2 (CH pc pb st) <= 2^37 - 2^24 -> zlen (CH pc pb st) <= SMAX + 2^15 - 1 ->
  (forall st' mo', INV pc pb st' mo' -> same_core st st' -> emb_sz st <= emb_sz st' <= emb_sz st + 110 -> atot (k st') mo' P) ->
  atot (exh_report ATOP RESV c st k) mo P.
Proof.
  intros R P pc pb c st k mo HI Hc Hroom HSB HSL Hk. unfold exh_report.
  destruct (exh_mem c st); [apply Hk; [exact HI| apply same_core_refl| lia]|].
  pose proof (exh_len2_bound c) as L2.
  assert (HI0 : INV pc pb (exh_set c st) mo) by (unfold exh_set; apply INV_set_exh; exact HI).
  apply (emb_append_ok R P pc pb (exh_set c st) EXH_LEN1 _ mo HI0); try (unfold EXH_LEN1; lia); try assumption.
  { unfold EXH_LEN1. change (emb_sz (exh_set c st)) with (emb_sz st). lia. }
  intros st1 mo1 HI1 SC1 EX1 ES1. change (emb_sz (exh_set c st)) with (emb_sz st) in ES1.
  assert (SC01 : same_core st st1) by (eapply same_core_trans; [apply same_core_set_exh| exact SC1]).
  apply (emb_append_ok R P pc pb st1 (exh_len2 c) _ mo1 HI1); try lia.
  - unfold EXH_LEN1 in ES1. lia.
  - rewrite (CH_same_core pc pb st st1 SC01). exact HSB.
  - rewrite (CH_same_core pc pb st st1 SC01). exact HSL.
  - intros st2 mo2 HI2 SC2 EX2 ES2. apply Hk; [exact HI2| eapply same_core_trans; [exact SC01| exact SC2]|]. unfold EXH_LEN1 in ES1. lia.
Qed.

Lemma cache_alloc_g_ok : forall R (P : R -> Model -> Prop) (pop : astate -> Z -> Z -> (astate -> bool -> AM R) -> AM R)
    (FL : astate -> Model -> Prop) pc pb st c n (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 0 <= n <= 64512 -> prim_cls_ok c n ->
  zsum2 (CHX pc pb st) <= 2^37 ->
  (forall req (k' : astate -> bool -> AM R), 0 < req -> req * size_of_class c <= K_USER_MAP -> c_count (get_cls st c) <= 0 ->
     req + c_num_freed (get_cls st c) <= 8 ->
     (forall st' mo', INV pc pb st' mo' -> same_but c (init_cache st) st' ->
        c_count (get_cls st' c) = c_count (get_cls (init_cache st) c) ->
        c_num_freed (get_cls (init_cache st) c) + req <= c_num_freed (get_cls st' c) ->
        atot (k' st' true) mo' P) ->
     (forall st' mo', FL st' mo' -> atot (k' st' false) mo' P) ->
     atot (pop (init_cache st) c req k') mo P) ->
  (forall st' mo', INV (CPrim c n :: pc) pb st' mo' -> (same_but c st st' \/ same_but c (init_cache st) st') ->
     atot (k st' true) mo' P) ->
  (forall st' mo', FL st' mo' -> atot (k st' false) mo' P) ->
  atot (cache_alloc_g pop st c k) mo P.
Proof.
  intros R P pop FL pc pb st c n k mo HI Hn Hcl HSB HPOP Hk Hkf.
  pose proof (prim_cls_facts c n Hn Hcl) as (F1 & F3 & F4 & F5 & F6).
  assert (Hc : 1 <= c <= 31) by lia.
  assert (Hwf : chunk_wf (CPrim c n)) by (cbn; split; [exact Hn| exact Hcl]).
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb st) /\ 0 <= nbatch c (qbatches pb st)).
  { split; [apply cntP_nonneg|]. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_nonneg| lia]. }
  assert (REPC : forall st0 r', INV pc pb st0 mo -> all_chunks pc pb st0 = all_chunks pc pb st -> qbatches pb st0 = qbatches pb st ->
            CLSOK (CPrim c n :: pc) pb st0 c r' -> cls_mapped_bytes' (get_cls st0 c) <= cls_mapped_bytes' r' ->
            c_mapped_user r' <= c_mapped_user (get_cls st0 c) ->
            INV (CPrim c n :: pc) pb (put_cls c r' st0) mo).
  { intros st0 r' HI0 E1 E2 HR Hm Hmu. apply (INV_repc pc); auto.
    - constructor; [exact Hwf|]. destruct HA as (_ & Hall & _). unfold all_chunks in Hall. apply Forall_app in Hall as [Hpc _]. exact Hpc.
    - intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia. }
  unfold cache_alloc_g. cbv zeta.
  destruct (Z.ltb_spec 0 (c_count (get_cls st c))) as [Hpos|Hz].
  -
    apply Hk; [|left; apply same_but_put].
    apply REPC; auto. all: try (unfold cls_mapped_bytes'; cproj; lia).
    unfold CLSOK. cproj. rewrite all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. repeat split; try lia.
  - rewrite max_count_init_cache, get_cls_init_cache.
    assert (Hhalf : 1 <= max_cached c / 2 <= 8 /\ 2 * (max_cached c / 2) <= max_cached c).
    { split. split; [apply Z.div_le_lower_bound|apply Z.div_le_upper_bound]; lia. apply Z.mul_div_le; lia. }
    set (m := max_cached c / 2) in *. clearbody m.
    pose proof (INV_init_cache _ _ _ _ HI) as HI1.
    destruct (Z.leb_spec m (c_num_freed (get_cls st c))) as [Hen|Hlt].
    +
      destruct (Z.ltb_spec (c_num_freed (get_cls st c)) m); [lia|].
      apply Hk; [|right; apply same_but_put].
      apply REPC; auto; rewrite ?all_chunks_init_cache, ?qbatches_init_cache, ?get_cls_init_cache; try reflexivity.
      all: try (unfold cls_mapped_bytes'; cproj; lia).
      unfold CLSOK. cproj. rewrite max_count_init_cache, all_chunks_init_cache, qbatches_init_cache, all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. repeat split; try lia.
    +
      apply (HPOP (m - c_num_freed (get_cls st c)) _ ltac:(lia)).
      * apply Z.le_trans with (m * size_of_class c); [apply Z.mul_le_mono_nonneg_r; lia| lia].
      * lia.
      * lia.
      * intros st2 mo2 HI2 HSB2 Ecnt Enf. cbv beta iota. rewrite get_cls_init_cache in Ecnt, Enf.
        destruct (Z.ltb_spec (c_num_freed (get_cls st2 c)) m); [lia|].
        pose proof HI2 as [HA2 HM2]. pose proof (AINV_cls _ _ _ _ HA2 Hc) as (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10).
        assert (AC : all_chunks pc pb st2 = all_chunks pc pb st /\ qbatches pb st2 = qbatches pb st).
        { destruct HSB2 as (_&_&_&_&_&Hl&_&Hq1&_&Hq2&_&_). unfold all_chunks, qbatches, live_chunks. unfold init_cache in Hl, Hq1, Hq2.
          destruct (a_cinit st); cbn in Hl, Hq1, Hq2; rewrite Hl, Hq1, Hq2; split; reflexivity. }
        destruct AC as [AC1 AC2].
        apply Hk. 2:{ right. eapply same_but_trans; [exact HSB2| apply same_but_put]. }
        apply (INV_repc pc); auto.
        -- constructor; [exact Hwf|]. destruct HA as (_ & Hall & _). unfold all_chunks in Hall. apply Forall_app in Hall as [Hpc _]. exact Hpc.
        -- intros c' Hc' Hne. rewrite cntP_cons. cbn [is_prim_of]. replace (c =? c') with false by (symmetry; apply Z.eqb_neq; lia). lia.
        -- unfold CLSOK. cproj. rewrite all_chunks_cons, cntP_cons. cbn [is_prim_of]. rewrite Z.eqb_refl. rewrite AC1, AC2 in D10. rewrite AC1, AC2.
           rewrite (max_count_same_but _ _ _ c HSB2), max_count_init_cache in *. repeat split; try lia.
        -- unfold cls_mapped_bytes'. cproj. lia.
        -- cproj. lia.
      * intros st2 mo2 HF. cbv beta iota. exact (Hkf st2 mo2 HF).
Qed.

Lemma cache_alloc_ok : forall R (P : R -> Model -> Prop) pc pb st c n (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 0 <= n <= 64512 -> prim_cls_ok c n ->
  size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + 8) + 2^20 <= K_FREEARR_OFF ->
  zsum2 (CHX pc pb st) <= 2^37 ->
  (forall st' mo', INV (CPrim c n :: pc) pb st' mo' -> (same_but c st st' \/ same_but c (init_cache st) st') ->
     atot (k st' true) mo' P) ->
  atot (cache_alloc st c k) mo P.
Proof.
  intros R P pc pb st c n k mo HI Hn Hcl Hroom HSB Hk. unfold cache_alloc.
  pose proof (prim_cls_facts c n Hn Hcl) as (F1 & F3 & F4 & F5 & F6).
  assert (Hc : 1 <= c <= 31) by lia.
  pose proof HI as [HA HM]. pose proof (AINV_cls _ _ _ _ HA Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
  assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb st) /\ 0 <= nbatch c (qbatches pb st)).
  { split; [apply cntP_nonneg|]. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_nonneg| lia]. }
  apply (cache_alloc_g_ok R P populate_free_array (fun _ _ => False) pc pb st c n k mo HI Hn Hcl HSB); [| exact Hk| intros ? ? []].
  intros req k' Hreq Hrs Hcz Hnf Hks _.
  apply (populate_ok R P pc pb (init_cache st) c req k' mo (INV_init_cache _ _ _ _ HI) Hc ltac:(lia) Hreq Hrs).
  - rewrite get_cls_init_cache. rewrite C10.
    assert (size_of_class c * c_num_freed (get_cls st c) <= size_of_class c * 8) by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (size_of_class c * c_count (get_cls st c) = 0) by (replace (c_count (get_cls st c)) with 0 by lia; ring).
    nia || lia.
  - rewrite ?CHX_init_cache. exact HSB.
  - exact Hks.
Qed.

Lemma cache_alloc_x_ok : forall R (P : R -> Model -> Prop) pc pb st c n (k : astate -> bool -> AM R) mo,
  INV pc pb st mo -> 0 <= n <= 64512 -> prim_cls_ok c n ->
  (c = K_BATCH_CLASS ->
     size_of_class c * (cntP c (all_chunks pc pb st) + nbatch c (qbatches pb st) + 8) + 2^20 <= K_FREEARR_OFF) ->
  zsum2 (CHX pc pb st) <= 2^37 ->
  emb_sz st + 110 <= EMB_MAX - 4096 -> zsum2 (CH pc pb st) <= 2^37 - 2^24 -> zlen (CH pc pb st) <= SMAX + 2^15 - 1 ->
  (forall st' mo', INV (CPrim c n :: pc) pb st' mo' -> (same_but c st st' \/ same_but c (init_cache st) st') ->
     atot (k st' true) mo' P) ->
  (forall st' mo', c <> K_BATCH_CLASS -> K_FREEARR_OFF < c_mapped_user (get_cls st c) + K_USER_MAP ->
     INV pc pb st' mo' -> same_core (init_cache st) st' -> emb_sz st <= emb_sz st' <= emb_sz st + 110 ->
     atot (k st' false) mo' P) ->
  atot (cache_alloc_x ATOP RESV st c k) mo P.
Proof.
  intros R P pc pb st c n k mo HI Hn Hcl Hroom24 HSB HEr HSB2 HSL Hk Hkf. unfold cache_alloc_x.
  pose proof (prim_cls_facts c n Hn Hcl) as (F1 & F3 & F4 & F5 & F6).
  assert (Hc : 1 <= c <= 31) by lia.
  apply (cache_alloc_g_ok R P (populate_free_array_x ATOP RESV)
           (fun st' mo' => (c <> K_BATCH_CLASS /\ K_FREEARR_OFF < c_mapped_user (get_cls st c) + K_USER_MAP) /\ INV pc pb st' mo' /\ same_core (init_cache st) st' /\ emb_sz st <= emb_sz st' <= emb_sz st + 110)
           pc pb st c n k mo HI Hn Hcl HSB); [| exact Hk| intros st' mo' ([X1 X2] & A & B & C); exact (Hkf st' mo' X1 X2 A B C)].
  intros req k' Hreq Hrs Hcz Hnf Hks Hkf'. unfold populate_free_array_x.
  pose proof (INV_init_cache _ _ _ _ HI) as HI1.
  destruct (Z.eqb_spec c K_BATCH_CLASS) as [E24|N24].
  {
    pose proof HI as [HA0 _]. pose proof (AINV_cls _ _ _ _ HA0 Hc) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10).
    assert (Hcnt0 : 0 <= cntP c (all_chunks pc pb st) /\ 0 <= nbatch c (qbatches pb st)).
    { split; [apply cntP_nonneg|]. unfold nbatch. destruct (c =? K_BATCH_CLASS); [apply zlen_nonneg| lia]. }
    apply (populate_ok R P pc pb (init_cache st) c req k' mo HI1 Hc ltac:(lia) Hreq Hrs).
    - rewrite get_cls_init_cache. rewrite C10. specialize (Hroom24 E24).
      assert (size_of_class c * c_num_freed (get_cls st c) <= size_of_class c * 8) by (apply Z.mul_le_mono_nonneg_l; lia).
      assert (size_of_class c * c_count (get_cls st c) = 0) by (replace (c_count (get_cls st c)) with 0 by lia; ring).
      nia || lia.
    - rewrite ?CHX_init_cache. exact HSB.
    - exact Hks. }
  assert (SCI : same_core st (init_cache st)) by (unfold init_cache; destruct (a_cinit st); [apply same_core_refl|]; unfold same_core; repeat split; reflexivity).
  apply (populate_g_ok R P _ _ pc pb (init_cache st) c req k' mo (fun s => or_intror eq_refl) HI1 Hc ltac:(lia) Hreq Hrs); [| rewrite ?CHX_init_cache; exact HSB| exact Hks].
  intros HEX. rewrite get_cls_init_cache in HEX. assert (ESI : emb_sz (init_cache st) = emb_sz st) by (unfold init_cache; destruct (a_cinit st); reflexivity).
  apply (exh_report_ok R P pc pb c (init_cache st) _ mo HI1 Hc); rewrite ?ESI, ?(CH_same_core pc pb st (init_cache st) SCI); try assumption.
  intros st' mo' HI' SC' ES'. apply Hkf'. split; [split; [exact N24| exact HEX]|]. split; [exact HI'|]. split; [exact SC'| exact ES'].
Qed.

Lemma large_alloc_ok : forall R (P : R -> Model -> Prop) pc pb st n (k : astate -> option achunk -> AM R) mo,
  INV pc pb st mo -> 64512 < n <= 2^32 - 2^20 ->
  zsum2 (CHX pc pb st) + sec_map_size n <= 2^37 - 2^18 -> a_nsec st < 2^20 - K_CHUNKS_BLOCK ->
  (forall st' mo' mb, INV (CSec mb (sec_map_size n) n :: pc) pb st' mo' ->
      (st' = set_nsec (a_nsec st + 1) st \/ st' = set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st)) ->
      atot (k st' (Some (CSec mb (sec_map_size n) n))) mo' P) ->
  (vm_gap_available (m_vmmaps mo) (sec_map_size n) = false -> atot (k st None) mo P) ->
  atot (large_alloc ATOP RESV st n k) mo P.
Proof.
  intros R P pc pb st n k mo HI Hn HSB HSL Hk HkN.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  pose proof (sec_map_size_bounds n ltac:(lia)) as SB.
  assert (MSA : sec_map_size n mod 4096 = 0).
  { unfold sec_map_size, rup, PG. match goal with |- ?x mod 4096 = 0 => replace x with ((((needed_size n + 4096 - 1) / 4096) + 1) * 4096) by lia end. apply Z_mod_mult. }
  unfold large_alloc. unfold ev. apply atotal_vis.
  { apply (INV_grant_aok pc pb st mo n HI ltac:(lia)). lia. }
  intros z mo' Hpost. cbn [apost] in Hpost.
  assert (ML : mmap_len (sec_map_size n) = sec_map_size n) by (apply mmap_len_id; lia). rewrite ML in Hpost.
  destruct Hpost as [(-> & -> & NG)|(Z1 & Z2 & Z3 & Z4 & ->)].
  {
    assert (E1 : mmap_answer_ok ATOP (sec_map_size n) (TWO64 - 12) = true) by (unfold mmap_answer_ok, is_err, TWO64; reflexivity).
    rewrite E1. cbn [negb]. assert (E2 : is_err (TWO64 - 12) = true) by (unfold is_err, TWO64; reflexivity). rewrite E2. exact (HkN NG). }
  assert (RUP : rup (sec_map_size n) PG = sec_map_size n).
  { unfold rup, PG. pose proof (Z.div_mod (sec_map_size n) 4096 ltac:(lia)) as Hd. rewrite MSA in Hd.
    replace (sec_map_size n + 4096 - 1) with (sec_map_size n / 4096 * 4096 + 4095) by lia. rewrite Z.div_add_l by lia. change (4095/4096) with 0. lia. }
  assert (Hok : mmap_answer_ok ATOP (sec_map_size n) z = true).
  { unfold mmap_answer_ok. rewrite RUP. apply orb_true_iff. right. unfold TWO64, PG.
    rewrite (proj2 (Z.ltb_lt 0 z)) by lia. rewrite Z1. cbn [Z.eqb andb]. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. }
  rewrite Hok. cbn [negb]. rewrite is_err_small by (unfold TWO64; lia).
  pose proof (grant_range pc pb st mo z (sec_map_size n) HI Z2 ltac:(lia) Z3 Z4) as Hrange.

  pose proof (grant_avoids pc pb st mo z (sec_map_size n) HI Z2 ltac:(lia) Z3 Z4) as HAV.
  rewrite HAV. cbn [andb negb].

  set (ch := CSec z (sec_map_size n) n).
  set (st1 := set_nsec (a_nsec st + 1) st).
  assert (HI1 : INV (ch :: pc) pb st1 (grant_model mo z (sec_map_size n))).
  { destruct HI as [HA HM]. split.
    - unfold AINV in *. destruct HA as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
      unfold st1. cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec a_cinit] in *.
      rewrite all_chunks_set_nsec, all_chunks_cons.
      change (qbatches pb (set_nsec (a_nsec st + 1) st)) with (qbatches pb st).
      change (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)) with (sec_of ch ++ CH pc pb st).
      split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec] in *.
               rewrite all_chunks_set_nsec, all_chunks_cons, cntP_cons. cbn [is_prim_of]. change (qbatches pb (set_nsec (a_nsec st + 1) st)) with (qbatches pb st). rewrite Z.add_0_l. exact X. }
      split. { constructor; [|exact H2]. cbn. split; [lia|]. split; [reflexivity|]. split; [lia|]. split; [lia|]. exact Hrange. }
      split; [exact H3|]. split; [exact H4|]. split; [exact H5|].
      split. { unfold ch. cbn [sec_of app]. rewrite zlen_cons. lia. }
      split; [exact H7|]. split; [exact H8|]. unfold live_budget, live_chunks in *. cbn [a_live set_nsec]. exact H9.
    - unfold st1. change (CHX (ch :: pc) pb (set_nsec (a_nsec st + 1) st)) with ((z, sec_map_size n) :: CHX pc pb st).
      apply (AMI_mono _ st); try reflexivity; try (unfold commit_bytes, csum, get_cls; cbn; lia); try (intros c0 _; apply Z.le_refl).
      apply AMI_grant; auto; lia. }
  destruct (Z.eqb_spec (a_nsec st) (a_nres st)) as [Heq|Hne].
  2:{ apply Hk; [exact HI1| left; reflexivity]. }

  destruct HI as [HA HM]. pose proof HA as (_ & _ & _ & _ & _ & Hnsec & Hres & _).
  destruct Hres as (j & Hj & Hres). assert (Hj63 : j <= 62) by (unfold K_CHUNKS_BLOCK in *; lia).
  destruct (Z.ltb_spec K_PTRARR_RESERVE (8 * (a_nres st + K_CHUNKS_BLOCK))) as [X|_]; [unfold K_PTRARR_RESERVE, K_CHUNKS_BLOCK in *; lia|].
  destruct (INV_ptr _ _ _ _ HI1) as (HinP & P2 & PRF). unfold st1 in HinP, P2, PRF. cbn [a_ptr_array set_nsec] in HinP, P2, PRF.
  destruct (AINV_geom _ _ _ HA) as (_ & _ & G3 & G4).
  assert (HBS : B (went (a_ptr_array st, PTR_SZ)) = a_ptr_array st /\ S (went (a_ptr_array st, PTR_SZ)) = PTR_SZ).
  { unfold B, S, went. cbn [fst snd]. unfold ACEIL, PTR_SZ, KHIGH in *. rewrite !unsigned_lit by lia. lia. }
  destruct HBS as [HB1 HS1].
  set (pa := a_ptr_array st + 8 * a_nres st).
  assert (PA1 : a_ptr_array st <= pa /\ pa + K_PTRARR_COMMIT <= a_ptr_array st + PTR_SZ /\ pa mod 4096 = 0 /\ 0 < pa).
  { unfold pa. rewrite Hres. unfold K_CHUNKS_BLOCK, K_PTRARR_COMMIT, PTR_SZ. repeat split; lia. }
  destruct PA1 as (PA1 & PA2 & PA3 & PA4).
  apply atotal_vis.
  { apply (INV_fixed_aok (ch :: pc) pb st1 _ (went (a_ptr_array st, PTR_SZ)) pa K_PTRARR_COMMIT HI1 HinP).
    - rewrite HB1. exact PA1.
    - rewrite HB1, HS1. exact PA2.
    -
      apply (region_free_sub _ (a_ptr_array st) PTR_SZ); [exact PRF| | | | |]; unfold K_PTRARR_COMMIT, PTR_SZ in *; lia.
    - exact PA4.
    - exact PA3.
    - reflexivity.
    - unfold K_PTRARR_COMMIT. lia.
    - change (CHX (ch :: pc) pb st1) with ((z, sec_map_size n) :: CHX pc pb st). cbn [zsum2 snd]. lia. }
  intros z2 mo2 Hpost2. cbn [apost] in Hpost2.
  assert (Hpz : (pa =? 0) = false) by (apply Z.eqb_neq; lia). fold pa in Hpost2. rewrite Hpz in Hpost2. destruct Hpost2 as [-> ->].
  fold pa. rewrite fixed_answer_ok_self. cbn [negb]. rewrite is_err_small by (unfold TWO64, ACEIL, KHIGH, PTR_SZ, K_PTRARR_COMMIT in *; lia).
  apply Hk; [| right; reflexivity].
  assert (ML2 : mmap_len K_PTRARR_COMMIT = K_PTRARR_COMMIT) by reflexivity. rewrite ML2.
  destruct HI1 as [HA1 HM1]. split.
  - unfold AINV in *. destruct HA1 as (HC & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
    unfold st1 in *. cbn [a_qloc_bytes a_qloc a_qglob_bytes a_qglob a_nsec a_nres a_live a_next a_space_beg a_ptr_array set_nsec set_nres a_cinit] in *.
    change (all_chunks (ch :: pc) pb (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (all_chunks (ch :: pc) pb (set_nsec (a_nsec st + 1) st)).
    change (qbatches pb (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (qbatches pb (set_nsec (a_nsec st + 1) st)).
    change (CH (ch :: pc) pb (set_nres (a_nres st + K_CHUNKS_BLOCK) (set_nsec (a_nsec st + 1) st))) with (CH (ch :: pc) pb (set_nsec (a_nsec st + 1) st)).
    split. { intros c Hc. pose proof (HC c Hc) as X. unfold cls_inv in *. unfold get_cls, max_count in *. cbn [a_cls a_cinit set_nsec set_nres] in *. exact X. }
    repeat (split; [assumption|]). split; [exists (j + 1); split; [lia| rewrite Hres; lia]|]. split; [exact H8|]. unfold live_budget, live_chunks in *. cbn [a_live set_nsec set_nres] in *. exact H9.
  - change (CHX (ch :: pc) pb (set_nres (a_nres st + K_CHUNKS_BLOCK) st1)) with (CHX (ch :: pc) pb st1).
    apply (AMI_commit _ st1 _ _ (went (a_ptr_array st, PTR_SZ)) pa K_PTRARR_COMMIT HM1 HinP).
    + rewrite HB1. exact PA1.
    + rewrite HB1, HS1. exact PA2.
    + exact PA3.
    + reflexivity.
    + unfold K_PTRARR_COMMIT. lia.
    + reflexivity.
    + reflexivity.
    + unfold st1, commit_bytes, csum, get_cls. cbn. unfold K_CHUNKS_BLOCK, K_PTRARR_COMMIT. lia.
    + intros x Hx. left. exact Hx.
Qed.

Definition mkch (n mb ms : Z) : achunk := if is_primary n then CPrim (class_id (needed_size n)) n else CSec mb ms n.

Definition csig (ch : achunk) : Z + Z := match ch with CPrim c _ => inl c | CSec _ _ n => inr n end.
Lemma live_budget_list_sig : forall ch ch' L, csig ch = csig ch' -> live_budget_list (ch :: L) -> live_budget_list (ch' :: L).
Proof.
  intros ch ch' L Hs (B1 & B2 & B3). unfold live_budget_list.
  destruct ch as [c n|mb ms n], ch' as [c' n'|mb' ms' n']; cbn in Hs; try discriminate; injection Hs as E; subst.
  - split; [|split; assumption]. rewrite cntP_cons in *. cbn [is_prim_of] in *. exact B1.
  - split; [|split]. { rewrite cntP_cons in *. cbn [is_prim_of] in *. exact B1. }
    { rewrite secs_cons, zlen_app in *. cbn [sec_of] in *. unfold zlen in *. cbn [length] in *. lia. }
    { cbn [secbytes] in *. lia. }
Qed.

Lemma sec_map_size_ge : forall n, 64512 < n -> n + 8192 <= sec_map_size n.
Proof.
  intros n Hn. unfold sec_map_size, needed_size. rewrite large_not_primary by lia. unfold needed0, rounded_size.
  assert (Hr : rz_size n = 2048) by (unfold rz_size, rz_log; repeat (rewrite (proj2 (Z.leb_gt _ _)) by lia); reflexivity). rewrite Hr.
  pose proof (rup_ge (Z.max n 8) 8 ltac:(lia)). pose proof (rup_ge (rup (Z.max n 8) 8 + 2048 + 2048) PG ltac:(unfold PG; lia)). unfold PG in *. lia.
Qed.

Lemma not_primary_large : forall n, 0 <= n -> is_primary n = false -> 64512 < n.
Proof.
  intros n Hn Hp. destruct (Z_lt_dec 64512 n); [lia|]. rewrite is_primary_iff in Hp by lia. apply Z.leb_gt in Hp. lia.
Qed.

Definition malloc_post (st : astate) (n : Z) (r : astate * option AsanCtrl.aptr) (mo' : Model) : Prop :=
  (exists ch, snd r = Some (a_next st) /\ INV [] [] (fst r) mo' /\ a_live (fst r) = <[a_next st := ch]> (a_live st)
     /\ (a_live st) !! (a_next st) = None /\ chunk_size ch = n
     /\ a_qloc_bytes (fst r) = a_qloc_bytes st /\ a_qglob_bytes (fst r) = a_qglob_bytes st /\ a_qloc (fst r) = a_qloc st /\ a_qglob (fst r) = a_qglob st
     /\ a_emb (fst r) = a_emb st
     /\ (is_primary n = false -> cls_keep K_BATCH_CLASS st (fst r)))
  \/ (snd r = None /\ INV [] [] (fst r) mo' /\ a_live (fst r) = a_live st /\ a_next (fst r) = a_next st
     /\ a_qloc_bytes (fst r) = a_qloc_bytes st /\ a_qglob_bytes (fst r) = a_qglob_bytes st /\ a_qloc (fst r) = a_qloc st /\ a_qglob (fst r) = a_qglob st
     /\ emb_sz st <= emb_sz (fst r) <= emb_sz st + 110
     /\ (is_primary n = false -> cls_keep K_BATCH_CLASS st (fst r))).

Theorem amalloc_core_g : forall (NN : Prop) st mo n,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> 0 <= n <= 2^32 - 2^20 ->
  (forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st)) ->
  emb_sz st + 110 <= EMB_MAX - 4096 ->
  (is_primary n = true -> class_id (needed_size n) <> K_BATCH_CLASS ->
     K_FREEARR_OFF < c_mapped_user (get_cls st (class_id (needed_size n))) + K_USER_MAP -> NN) ->
  (is_primary n = false -> vm_gap_available (m_vmmaps mo) (sec_map_size n) = false -> NN) ->
  atot (amalloc ATOP RESV st n) mo (fun r mo' => malloc_post st n r mo' /\ (snd r = None -> NN)).
Proof.
  intros NN st mo n HI Hql Hqg Hn HLB HEr HNN1 HNN2.
  pose proof HI as [HA HM].
  assert (Hnone : (a_live st) !! (a_next st) = None).
  { destruct ((a_live st) !! (a_next st)) as [ch0|] eqn:E; [|reflexivity]. exfalso.
    destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ E). lia. }
  assert (HQB : bsum (qbatches [] st) <= 2^28 + 2^22).
  { unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hq1 & Hq2 & _). unfold Q_CACHE, Q_MAX in *. lia. }
  destruct (CH_bounds_gen [] [] st (2^28 + 2^22) HA HQB ltac:(lia) ltac:(unfold zlen; cbn; lia) ltac:(cbn; lia)) as [HCL HCS].
  assert (HCL2 : zlen (CH [] [] st) <= SMAX + 2^15 - 1) by (unfold SMAX in *; lia).
  assert (HCS2 : zsum2 (CH [] [] st) <= 2^37 - 2^24 - 2^32) by (unfold LSBYTES in *; lia).
  pose proof (emb_ent_zsum2 _ _ _ HA) as EZ. unfold EMB_MAX in EZ.
  assert (HCX : zsum2 (CHX [] [] st) <= 2^37 - 2^23 - 2^32) by (rewrite zsum2_CHX; lia).
  assert (Hnsec : a_nsec st < 2^20 - K_CHUNKS_BLOCK).
  { destruct HA as (_ & _ & _ & _ & _ & H6 & _). rewrite H6. unfold K_CHUNKS_BLOCK, SMAX in *. lia. }
  assert (Hns : needed_size n <= 2^40).
  { unfold needed_size, needed0, rounded_size. pose proof (rup_le (Z.max n 8) 8 ltac:(lia)).
    pose proof (rz_log_range n) as Hrl.
    assert (0 <= rz_size n <= 2048).
    { unfold rz_size. rewrite Z.shiftl_mul_pow2 by lia. change 2048 with (16 * 2^7).
      split. apply Z.mul_nonneg_nonneg; [lia|apply Z.pow_nonneg; lia]. apply Z.mul_le_mono_nonneg_l; [lia|apply Z.pow_le_mono_r; lia]. }
    destruct (is_primary n); lia. }
  unfold amalloc. destruct (Z.ltb_spec (2^40) n); [lia|]. destruct (Z.ltb_spec (2^40) (needed_size n)); [lia|]. cbn [orb].
  destruct (is_primary n) eqn:Hp.
  -
    pose proof (primary_class_facts n ltac:(lia) Hp) as F. cbv zeta in F. destruct F as (F1 & F2 & F3 & F4 & F5 & F6).
    set (c := class_id (needed_size n)) in *.
    assert (Hn64 : 0 <= n <= 64512) by (destruct (Z_lt_dec 64512 n) as [Hlt|]; [rewrite (large_not_primary n Hlt) in Hp; discriminate| lia]).
    assert (ROOM24 : c = K_BATCH_CLASS -> size_of_class c * (cntP c (all_chunks [] [] st) + nbatch c (qbatches [] st) + 8) + 2^20 <= K_FREEARR_OFF).
    { intros ->. apply (room24_of_AINV [] [] st HA HQB). vm_compute. discriminate. }
    apply (cache_alloc_x_ok _ _ [] [] st c n _ mo HI Hn64 (or_introl eq_refl) ROOM24); try lia.
    + intros st' mo' HI' HSB'.
      assert (HF : a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st /\ a_emb st' = a_emb st).
      { destruct HSB' as [X|X]; destruct X as (_&_&_&_&_&Hl&Hnx&Hq1&Hqb1&Hq2&Hqb2&_&Hemb); [repeat split; assumption|].
        unfold init_cache in *; destruct (a_cinit st); cbn in *; repeat split; assumption. }
      destruct HF as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
      cbv beta iota. apply atotal_ret. split; [| cbn [snd]; intros X; discriminate X]. left. exists (CPrim c n). cbn [fst snd]. rewrite E2, E1.
      split; [reflexivity|]. split.
      { rewrite <- E1, <- E2. apply INV_hand_to_live; [exact HI'|]. unfold live_chunks. rewrite E1. specialize (HLB 0 0). unfold mkch in HLB. rewrite Hp in HLB. exact HLB. }
      repeat split; auto; congruence.
    +
      intros st' mo' N24 HEX HI' SC' ES'. cbv beta iota. apply atotal_ret. split; [| cbn [snd]; intros _; exact (HNN1 eq_refl N24 HEX)]. right. cbn [fst snd].
      assert (SCI : same_core st (init_cache st)) by (unfold init_cache; destruct (a_cinit st); [apply same_core_refl|]; unfold same_core; repeat split; reflexivity).
      destruct (same_core_trans _ _ _ SCI SC') as (_&_&_&_&_&Hl&Hnx&Hq1&Hqb1&Hq2&Hqb2).
      split; [reflexivity|]. split; [exact HI'|]. repeat split; auto; try lia; congruence.
  -
    pose proof (not_primary_large n ltac:(lia) Hp) as Hbig. pose proof (sec_map_size_bounds n ltac:(lia)) as SB. pose proof (sec_map_size_ge n Hbig) as SG.
    apply (large_alloc_ok _ _ [] [] st n _ mo HI ltac:(lia) ltac:(lia) Hnsec).
    2:{
        intros NG. cbv beta iota. apply atotal_ret. split; [| cbn [snd]; intros _; exact (HNN2 eq_refl NG)]. right. cbn [fst snd]. split; [reflexivity|]. split; [exact HI|].
        repeat split; auto; lia. }
    intros st' mo' mb HI' Hst'.
    assert (HF : a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st /\ a_emb st' = a_emb st).
    { destruct Hst' as [-> | ->]; repeat split; reflexivity. }
    destruct HF as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    cbv beta iota. cbn [chunk_user_beg].
    pose proof HI' as [HA' HM']. pose proof HA' as (_ & HW' & _). rewrite all_chunks_cons in HW'. apply Forall_cons_iff in HW' as [Hwf _].
    cbn in Hwf. destruct Hwf as (_ & _ & Hal & Hmb & Hrange).
    assert (Hland : 0 <= Z.land n (Z.lnot 7) <= n).
    { rewrite <- Z.ldiff_land. change 7 with (Z.ones 3). rewrite Z.ldiff_ones_r by lia.
      rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia. pose proof (Z.div_mod n (2^3) ltac:(lia)). pose proof (Z.mod_pos_bound n (2^3) ltac:(lia)). lia. }
    unfold poison0.
    apply atotal_ret. split; [| cbn [snd]; intros X; discriminate X]. left. exists (CSec mb (sec_map_size n) n). cbn [fst snd]. rewrite E2, E1.
    split; [reflexivity|]. split.
    { rewrite <- E1, <- E2. apply INV_hand_to_live; [exact HI'|]. unfold live_chunks. rewrite E1. specialize (HLB mb (sec_map_size n)). unfold mkch in HLB. rewrite Hp in HLB. exact HLB. }
    repeat split; auto; destruct Hst' as [-> | ->]; reflexivity.
Qed.

Theorem amalloc_core : forall st mo n,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> 0 <= n <= 2^32 - 2^20 ->
  (forall mb ms, live_budget_list (mkch n mb ms :: live_chunks st)) ->
  emb_sz st + 110 <= EMB_MAX - 4096 ->
  atot (amalloc ATOP RESV st n) mo (malloc_post st n).
Proof.
  intros st mo n HI Hql Hqg Hn HLB HEr.
  eapply atotal_mono; [| apply (amalloc_core_g True st mo n HI Hql Hqg Hn HLB HEr); intros; exact I].
  intros r mo' [H _]. exact H.
Qed.

Theorem aaligned16x_core : forall st mo n,
  INV [] [] st mo -> a_qloc_bytes st <= Q_CACHE -> a_qglob_bytes st <= Q_MAX -> 16 <= n <= ALIGNED_NMAX -> n mod 16 = 0 ->
  emb_sz st + 110 <= EMB_MAX - 4096 ->
  atot (aaligned16x ATOP RESV st n) mo (malloc_post st n).
Proof.
  intros st mo n HI Hql Hqg Hn Hm HEr.
  pose proof HI as [HA HM].
  assert (Hnone : (a_live st) !! (a_next st) = None).
  { destruct ((a_live st) !! (a_next st)) as [ch0|] eqn:E; [|reflexivity]. exfalso.
    destruct HA as (_ & _ & _ & _ & _ & _ & _ & Hid & _). specialize (Hid _ _ E). lia. }
  assert (HQB : bsum (qbatches [] st) <= 2^28 + 2^22).
  { unfold qbatches. cbn [app]. rewrite bsum_app. destruct HA as (_ & _ & _ & Hq1 & Hq2 & _). unfold Q_CACHE, Q_MAX in *. lia. }
  destruct (CH_bounds_gen [] [] st (2^28 + 2^22) HA HQB ltac:(lia) ltac:(unfold zlen; cbn; lia) ltac:(cbn; lia)) as [HCL HCS].
  assert (HCL2 : zlen (CH [] [] st) <= SMAX + 2^15 - 1) by (unfold SMAX in *; lia).
  assert (HCS2 : zsum2 (CH [] [] st) <= 2^37 - 2^24 - 2^32) by (unfold LSBYTES in *; lia).
  pose proof (emb_ent_zsum2 _ _ _ HA) as EZ. unfold EMB_MAX in EZ.
  assert (HCX : zsum2 (CHX [] [] st) <= 2^37 - 2^23 - 2^32) by (rewrite zsum2_CHX; lia).
  pose proof (al16_facts n Hn Hm) as F. cbv zeta in F. destruct F as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
  assert (Hn64 : 0 <= n <= 64512) by (unfold ALIGNED_NMAX in Hn; lia).
  unfold aaligned16x. cbv zeta. set (c := class_id (needed16 n)) in *.
  assert (HLB : live_budget_list (CPrim c n :: live_chunks st)).
  { destruct HA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HLB & _). apply live_budget_list_iff in HLB.
    destruct HLB as (B1 & B2 & B3). unfold live_budget_list. rewrite cntP_cons. cbn [is_prim_of].
    replace (c =? K_BATCH_CLASS) with false by (symmetry; apply Z.eqb_neq; exact F7).
    split; [lia|]. split; [exact B2| exact B3]. }
  apply (cache_alloc_x_ok _ _ [] [] st c n _ mo HI Hn64 (or_intror (conj eq_refl (conj Hn Hm))) (fun E24 => False_ind _ (F7 E24))); try lia.
  - intros st' mo' HI' HSB'.
    assert (HF : a_live st' = a_live st /\ a_next st' = a_next st /\ a_qloc_bytes st' = a_qloc_bytes st /\ a_qglob_bytes st' = a_qglob_bytes st /\ a_qloc st' = a_qloc st /\ a_qglob st' = a_qglob st /\ a_emb st' = a_emb st).
    { destruct HSB' as [X|X]; destruct X as (_&_&_&_&_&Hl&Hnx&Hq1&Hqb1&Hq2&Hqb2&_&Hemb); [repeat split; assumption|].
      unfold init_cache in *; destruct (a_cinit st); cbn in *; repeat split; assumption. }
    destruct HF as (E1 & E2 & E3 & E4 & E5 & E6 & E7).
    cbv beta iota. apply atotal_ret. left. exists (CPrim c n). cbn [fst snd]. rewrite E2, E1.
    split; [reflexivity|]. split.
    { rewrite <- E1, <- E2. apply INV_hand_to_live; [exact HI'|]. unfold live_chunks. rewrite E1. exact HLB. }
    repeat split; auto; congruence.
  - intros st' mo' _ _ HI' SC' ES'. cbv beta iota. apply atotal_ret. right. cbn [fst snd].
    assert (SCI : same_core st (init_cache st)) by (unfold init_cache; destruct (a_cinit st); [apply same_core_refl|]; unfold same_core; repeat split; reflexivity).
    destruct (same_core_trans _ _ _ SCI SC') as (_&_&_&_&Ecls&Hl&Hnx&Hq1&Hqb1&Hq2&Hqb2).
    split; [reflexivity|]. split; [exact HI'|]. repeat split; auto; try lia; unfold get_cls; rewrite ?Ecls; reflexivity.
Qed.

Lemma CHX_cons : forall ch pc pb st, CHX (ch :: pc) pb st = sec_of ch ++ CHX pc pb st.
Proof. intros. unfold CHX. rewrite CH_cons, app_assoc. reflexivity. Qed.

Lemma region_free_sep : forall l (a n : Z),
  Forall (fun e => bv_unsigned (fst e) + bv_unsigned (snd e) <= a \/ a + n <= bv_unsigned (fst e)) l -> 0 <= a -> a + n < 2^64 -> 0 <= n ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true.
Proof.
  induction l as [|[b s] l IH]; intros a n Hf Ha Han Hn; [reflexivity|].
  apply Forall_cons_iff in Hf as [H1 Hf]. cbn [region_free]. rewrite (IH a n Hf Ha Han Hn).
  unfold iv_overlap. rewrite !unsigned_lit by lia. cbn [fst snd] in H1.
  destruct H1 as [H1|H1].
  - replace (a <? bv_unsigned b + bv_unsigned s) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  - replace (bv_unsigned b <? a + n) with false by (symmetry; apply Z.ltb_ge; lia). rewrite andb_false_r. reflexivity.
Qed.

Lemma INV_madvise_aok : forall pc pb st mo mb ms,
  INV pc pb st mo -> 0 < mb -> 0 < ms <= 2^33 -> (mb + ms <= LS_LO \/ (KHIGH <= mb /\ mb + ms <= ATOP)) ->
  flush_beg mb < flush_end mb ms ->
  aok (AMadvise (flush_beg mb) (flush_end mb ms - flush_beg mb)) mo.
Proof.
  intros pc pb st mo mb ms HI Hmb Hms Hrange Hlt.
  destruct (INV_atop _ _ _ _ HI) as [[AT1 AT2] AT3]. unfold ACEIL, ATOP_MAX in AT1, AT2.
  destruct (INV_shadows _ _ _ _ HI) as (HinLS & HinGAP & HinHS).
  pose proof HI as [HA HM]. pose proof HM as (M1 & M2 & M3 & M4 & M5 & M6 & [M7 M7s] & M8 & M9 & MT & _).
  unfold flush_beg, flush_end in *. rewrite !Z.shiftr_div_pow2 in * by lia. change (2^3) with 8 in *.
  set (sb := SHADOW_OFF + mb / 8) in *. set (se := SHADOW_OFF + (mb + ms) / 8) in *.
  pose proof (rup_ge sb PG ltac:(unfold PG; lia)) as P1. pose proof (rup_mod sb PG ltac:(unfold PG; lia)) as P2.
  pose proof (rdn_le se PG ltac:(unfold PG; lia)) as P3. pose proof (rdn_mod se PG ltac:(unfold PG; lia)) as P4.
  set (pbg := rup sb PG) in *. set (pen := rdn se PG) in *. unfold PG in *.
  assert (SBE : 0x7fff8000 <= sb /\ se <= 0x10007fff8000 /\
               ((0x7fff7000 <= sb /\ se <= 0x8fff7000) \/ (0x2008fff7000 <= sb /\ se <= 0x10007fff8000))).
  { unfold sb, se, SHADOW_OFF, LS_LO, KHIGH in *. destruct Hrange as [LOW|[HI1 HI2]]; (split; [Z.div_mod_to_equations; lia|]); (split; [Z.div_mod_to_equations; lia|]); [left|right]; Z.div_mod_to_equations; lia. }
  destruct SBE as (SB1 & SB2 & SBC).
  assert (SLEN : se - sb <= ms / 8 + 1) by (unfold sb, se; Z.div_mod_to_equations; lia).
  assert (MS8 : ms / 8 <= 2^30) by (Z.div_mod_to_equations; lia).
  assert (LM : (pen - pbg) mod 4096 = 0) by (rewrite Zminus_mod, P2, P4; reflexivity).
  cbn [AsanNodeSem.aok]. split; [lia|]. split; [exact LM|]. split; [lia|]. split; [exact P2|]. split; [lia|]. split; [exact M1|].
  unfold Madvise.madvise_dontneed_ok. rewrite !andb_true_iff. split; [split|].
  - apply (region_free_above _ pbg (pen - pbg) RES_HI M3); unfold RES_HI; lia.
  - destruct SBC as [[L1 L2]|[H1 H2]].
    + apply (map_contains_In _ (went (LS_LO, LS_SZ))); [exact HinLS| |]; unfold went, LS_LO, LS_SZ; cbn [fst snd]; rewrite !unsigned_lit by lia; lia.
    + apply (map_contains_In _ (went (HS_LO, HS_SZ))); [exact HinHS| |]; unfold went, HS_LO, HS_SZ; cbn [fst snd]; rewrite !unsigned_lit by lia; lia.
  - apply region_free_sep; try lia. unfold noacc_sep in M7s. eapply Forall_impl; [| exact M7s]. cbv beta.
    intros e [[S1|S1] [S2|S2]]; unfold sepz, LS_LO, LS_SZ, HS_LO, HS_SZ in *; destruct SBC as [[L1 L2]|[H1 H2]]; lia.
Qed.

End WithResv.
