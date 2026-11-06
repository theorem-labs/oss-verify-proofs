(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow R_sizeclass.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface D_defs D_kit R_cache_defs R_prim_defs R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc R_quar_defs R_qput R_qenqueue R_qenqueue_N R_qenqueue_F R_asan_free R_prim_kit RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2 RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeI.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow R_sizeclass.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_cache_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_thread.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_m2s.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_leaves.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_poison.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_setshadow.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_glue_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_sec_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_depot_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_fs_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_tlsgetaddr.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_intalloc.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_quar_defs.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qput.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qenqueue.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qenqueue_N.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_qenqueue_F.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_asan_free.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_prim_kit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_state.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_rep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_frame.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_trans.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_facts0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_sep.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_malstate.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freelift.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_geo0.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_fkit.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freestate.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeA.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeA2.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freestmt.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeC.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeD.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeF.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeG.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_freeI.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fl_hit_w : forall {Y} (f : Z -> Y) (l : list Z) (chs : list Y), l <> [] -> firstn (length l) chs = map f l ->
  nth_error chs (length l - 1) = Some (f (last l 0)).
Proof.
  intros Y f l. induction l as [|x l IH]; intros chs Hne H; [exfalso; exact (Hne eq_refl)|].
  destruct chs as [|y chs]; [discriminate H|]. cbn [length firstn map] in H. injection H as Hy H.
  destruct l as [|x' l]; [cbn; rewrite Hy; reflexivity|].
  pose proof (IH chs ltac:(discriminate) H) as X. replace (length (x' :: l) - 1)%nat with (length l) in X by (cbn; lia).
  change (S (S (length l)) - 1)%nat with (S (length l)). cbn [nth_error last]. exact X.
Qed.

(* [comment removed for export] *)
Lemma fl_hit_addr : forall SB c j, 0 <= j -> 0 <= j * ClassSize c < 2 ^ 32 -> ClassSize c mod 16 = 0 ->
  chunk_addr SB c (cpw c j) = p_abeg SB c (Z.to_nat j).
Proof.
  intros SB c j Hj Hr Hm. unfold chunk_addr, cpw, cptr, p_abeg. rewrite Z2Nat.id by exact Hj.
  assert (Hd : 0 <= j * ClassSize c / 16 < 2 ^ 28) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite unsigned_lit by lia. rewrite Z.mod_small by lia.
  assert (E : j * ClassSize c = 16 * (j * ClassSize c / 16)).
  { apply Z.div_exact; [lia|]. rewrite Z.mul_comm. rewrite <- Zmult_mod_idemp_l. rewrite Hm. reflexivity. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma firstn_snoc_map : forall {Y} (f : Z -> Y) (l : list Z) x (chs : list Y), firstn (length (l ++ [x])) chs = map f (l ++ [x]) ->
  firstn (length l) chs = map f l.
Proof.
  intros Y f l x chs H. rewrite length_app in H. cbn [length] in H. rewrite map_app in H.
  assert (E : firstn (length l) (firstn (length l + 1) chs) = firstn (length l) (map f l ++ map f [x])) by (rewrite H; reflexivity).
  rewrite firstn_firstn, Nat.min_l in E by lia. rewrite firstn_app, length_map, Nat.sub_diag, firstn_O, app_nil_r in E.
  assert (E2 : firstn (length l) (map f l) = map f l) by (clear; induction l as [|a l IH]; [reflexivity | cbn; f_equal; exact IH]).
  rewrite E2 in E. exact E.
Qed.

Lemma fl_nodup_app_not_in : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros A l1 l2 x H H1 H2. apply in_split in H1 as (a & b & ->). rewrite <- app_assoc in H. cbn [app] in H.
  apply (NoDup_remove_2 _ _ _ H). apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.

(* [comment removed for export] *)
Lemma fl_CB_of_stk : forall (m : mem) a (k : nat), stk bsegs m a (a + Z.of_nat k) -> exists bs, rw_cells bsegs m a [CB k bs].
Proof.
  intros m a k St. destruct (stk_bytes bsegs m a (a + Z.of_nat k) St ltac:(lia)) as (bs & Hl & Hb).
  exists bs. split; [split|].
  - cbn. split; [lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. destruct St as (S0 & S1 & Sw). split; [lia|]. split; [lia|].
    intros j Hj. exact (proj1 (Sw (a + j) ltac:(lia))).
Qed.

(* [comment removed for export] *)
Lemma qenq_post_weaken : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) (fc : bv 32) W W' Q bs lo (m : mem)
    (P : mem -> Prop) ms,
  sub_fp W W' -> qenq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W Q bs lo m P ms ->
  qenq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W' Q bs lo m P ms.
Proof.
  intros until ms. intros HS (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & R).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|].
  split; [exact (munch_weaken _ _ _ _ HS MU) | exact R].
Qed.

(* [comment removed for export] *)
Lemma pop24_st : forall Σ1 cal jB c' i' st, nth_error (r_st (pr (pop24 Σ1 cal jB) c')) i' = Some st ->
  (c' = 24 /\ i' = jB /\ st = CkBatch) \/ ((c' <> 24 \/ i' <> jB) /\ nth_error (r_st (pr Σ1 c')) i' = Some st).
Proof.
  intros Σ1 cal jB c' i' st H. cbn [pr pop24] in H. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|right; split; [left; exact Hcc | exact H]].
  unfold upd_reg in H. cbn [r_st] in H. rewrite nth_error_upd_ck in H. destruct (Nat.eqb_spec jB i') as [<-|Hii].
  - destruct (Nat.ltb_spec jB (length (r_st (pr Σ1 24)))); [injection H as <-; left; tauto | discriminate].
  - right. split; [right; intros E; exact (Hii (eq_sym E)) | exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section New.
Variables (Σ : rtsA) (c : Z) (i : nat) (n : Z) (D' : depot) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW0 : rt_wf Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In (p_abeg (l_SB (lay Σ)) 24 j0) (map fst (ql Σ))).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation Σ1 := (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) D').
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

Let HG : geo_ok Σ := geo_of_wf Σ HW0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End New.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section New2.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (n : Z) (tr : list Z) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle /\ ql Σ = [])
  \/ (st0 = CkBatch /\ exists pre ents0, ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)] /\ length ents0 = 1021%nat).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
Hypothesis Dok : depot_ok (fst (depot_put (dep Σ) tr)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis Dinv : dep_inv (fst (depot_put (dep Σ) tr)).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation Σ1 := (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))).
#[local] Notation Σ2 := (enq_new (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) cal jB
                          (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

(* [comment removed for export] *)

End New2.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface D_defs D_kit R_sizeclass R_cache_defs R_prim_defs
  R_thread R_m2s R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc
  R_quar_defs R_qput R_qenqueue R_qenqueue_N R_qenqueue_F R_asan_free R_prim_kit
  RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_malstate RT_freelift RT_geo0 RT_fkit RT_freestate RT_freeA RT_freeA2
  RT_freestmt RT_freeC RT_freeD RT_freeF RT_freeG RT_freeI.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma fl_hit_w : forall {Y} (f : Z -> Y) (l : list Z) (chs : list Y), l <> [] -> firstn (length l) chs = map f l ->
  nth_error chs (length l - 1) = Some (f (last l 0)).
Proof.
  intros Y f l. induction l as [|x l IH]; intros chs Hne H; [exfalso; exact (Hne eq_refl)|].
  destruct chs as [|y chs]; [discriminate H|]. cbn [length firstn map] in H. injection H as Hy H.
  destruct l as [|x' l]; [cbn; rewrite Hy; reflexivity|].
  pose proof (IH chs ltac:(discriminate) H) as X. replace (length (x' :: l) - 1)%nat with (length l) in X by (cbn; lia).
  change (S (S (length l)) - 1)%nat with (S (length l)). cbn [nth_error last]. exact X.
Qed.

(* [comment removed for export] *)
Lemma fl_hit_addr : forall SB c j, 0 <= j -> 0 <= j * ClassSize c < 2 ^ 32 -> ClassSize c mod 16 = 0 ->
  chunk_addr SB c (cpw c j) = p_abeg SB c (Z.to_nat j).
Proof.
  intros SB c j Hj Hr Hm. unfold chunk_addr, cpw, cptr, p_abeg. rewrite Z2Nat.id by exact Hj.
  assert (Hd : 0 <= j * ClassSize c / 16 < 2 ^ 28) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  rewrite unsigned_lit by lia. rewrite Z.mod_small by lia.
  assert (E : j * ClassSize c = 16 * (j * ClassSize c / 16)).
  { apply Z.div_exact; [lia|]. rewrite Z.mul_comm. rewrite <- Zmult_mod_idemp_l. rewrite Hm. reflexivity. }
  lia.
Qed.

(* [comment removed for export] *)
Lemma firstn_snoc_map : forall {Y} (f : Z -> Y) (l : list Z) x (chs : list Y), firstn (length (l ++ [x])) chs = map f (l ++ [x]) ->
  firstn (length l) chs = map f l.
Proof.
  intros Y f l x chs H. rewrite length_app in H. cbn [length] in H. rewrite map_app in H.
  assert (E : firstn (length l) (firstn (length l + 1) chs) = firstn (length l) (map f l ++ map f [x])) by (rewrite H; reflexivity).
  rewrite firstn_firstn, Nat.min_l in E by lia. rewrite firstn_app, length_map, Nat.sub_diag, firstn_O, app_nil_r in E.
  assert (E2 : firstn (length l) (map f l) = map f l) by (clear; induction l as [|a l IH]; [reflexivity | cbn; f_equal; exact IH]).
  rewrite E2 in E. exact E.
Qed.

Lemma fl_nodup_app_not_in : forall {A} (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros A l1 l2 x H H1 H2. apply in_split in H1 as (a & b & ->). rewrite <- app_assoc in H. cbn [app] in H.
  apply (NoDup_remove_2 _ _ _ H). apply in_or_app. right. apply in_or_app. right. exact H2.
Qed.

(* [comment removed for export] *)
Lemma fl_CB_of_stk : forall (m : mem) a (k : nat), stk asegs m a (a + Z.of_nat k) -> exists bs, rw_cells asegs m a [CB k bs].
Proof.
  intros m a k St. destruct (stk_bytes asegs m a (a + Z.of_nat k) St ltac:(lia)) as (bs & Hl & Hb).
  exists bs. split; [split|].
  - cbn. split; [lia | exact I].
  - cbn [cells_bytes cbytes]. rewrite app_nil_r. exact Hb.
  - cbn [cells_size csize]. rewrite Nat.add_0_r. destruct St as (S0 & S1 & Sw). split; [lia|]. split; [lia|].
    intros j Hj. exact (proj1 (Sw (a + j) ltac:(lia))).
Qed.

(* [comment removed for export] *)
Lemma qenq_post_weaken : forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (F : bvmap 5 word) (fc : bv 32) W W' Q bs lo (m : mem)
    (P : mem -> Prop) ms,
  sub_fp W W' -> qenq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W Q bs lo m P ms ->
  qenq_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc W' Q bs lo m P ms.
Proof.
  intros until ms. intros HS (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & E & MU & R).
  exists t0', t1', t2', a0', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'. split; [exact E|].
  split; [exact (munch_weaken _ _ _ _ HS MU) | exact R].
Qed.

(* [comment removed for export] *)
Lemma pop24_st : forall Σ1 cal jB c' i' st, nth_error (r_st (pr (pop24 Σ1 cal jB) c')) i' = Some st ->
  (c' = 24 /\ i' = jB /\ st = CkBatch) \/ ((c' <> 24 \/ i' <> jB) /\ nth_error (r_st (pr Σ1 c')) i' = Some st).
Proof.
  intros Σ1 cal jB c' i' st H. cbn [pr pop24] in H. destruct (Z.eqb_spec c' 24) as [->|Hcc]; [|right; split; [left; exact Hcc | exact H]].
  unfold upd_reg in H. cbn [r_st] in H. rewrite nth_error_upd_ck in H. destruct (Nat.eqb_spec jB i') as [<-|Hii].
  - destruct (Nat.ltb_spec jB (length (r_st (pr Σ1 24)))); [injection H as <-; left; tauto | discriminate].
  - right. split; [right; intros E; exact (Hii (eq_sym E)) | exact H].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section New.
Variables (Σ : rtsA) (c : Z) (i : nat) (n : Z) (D' : depot) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HW0 : rt_wf Σ.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle) \/ (st0 = CkBatch /\ In (p_abeg (l_SB (lay Σ)) 24 j0) (map fst (ql Σ))).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation Σ1 := (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) D').
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

Let HG : geo_ok Σ := geo_of_wf Σ HW0.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

End New.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section New2.
Variables (Σ : rtsA) (m : mem) (c : Z) (i : nat) (n : Z) (tr : list Z) (cal : list Z) (jB j0 : nat) (st0 : ckst) (usp : Z).
Hypothesis HA : ART_A Σ m.
Hypothesis Hc : 1 <= c <= 31.
Hypothesis Hn : nth_error (r_st (pr Σ c)) i = Some (CkAlloc n).
Hypothesis HCA : ca Σ 24 = cal ++ [Z.of_nat jB].
Hypothesis Hj0 : nth_error (r_st (pr Σ 24)) j0 = Some st0.
Hypothesis Hvar : (j0 = jB /\ st0 = CkIdle /\ ql Σ = [])
  \/ (st0 = CkBatch /\ exists pre ents0, ql Σ = pre ++ [(p_abeg (l_SB (lay Σ)) 24 j0, ents0)] /\ length ents0 = 1021%nat).
Hypothesis Hsp : l_ACEIL (lay Σ) + 0x10000 <= usp.
Hypothesis Dok : depot_ok (fst (depot_put (dep Σ) tr)) (l_DNB (lay Σ)) (l_SSB (lay Σ)) (l_ACEIL (lay Σ)).
Hypothesis Dinv : dep_inv (fst (depot_put (dep Σ) tr)).
#[local] Notation L := (lay Σ).
#[local] Notation T := (l_T (lay Σ)).
#[local] Notation SB := (l_SB (lay Σ)).
#[local] Notation b0 := (p_abeg (l_SB (lay Σ)) 24 j0).
#[local] Notation bB := (p_abeg (l_SB (lay Σ)) 24 jB).
#[local] Notation M := (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16).
#[local] Notation Σ1 := (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))).
#[local] Notation Σ2 := (enq_new (free_p Σ c i n (p_abeg (l_SB (lay Σ)) c i + rz_size n) (fst (depot_put (dep Σ) tr))) cal jB
                          (p_abeg (l_SB (lay Σ)) c i + rz_size n - 16) n).
#[local] Notation W := (W_E (l_T (lay Σ)) (p_abeg (l_SB (lay Σ)) 24 j0) (p_abeg (l_SB (lay Σ)) 24 jB) usp).

(* [comment removed for export] *)

End New2.
