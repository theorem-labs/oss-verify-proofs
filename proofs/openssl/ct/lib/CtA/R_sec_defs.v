(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCtA.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Mem Cells Step Arr Frame Tac SysStep. 
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtA Require Import Layout R_cache_defs R_prim_defs R_glue_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Notation mem := (word -> option byte).

(* [comment removed for export] *)
Definition SEC : Z := INST + 0x40.        (* [comment removed for export] *)
Definition GSTAT : Z := INST + 0x2b0.     (* [comment removed for export] *)

(* [comment removed for export] *)
Definition roundup4k (z : Z) : Z := ((z + 4095) / 4096) * 4096.
Lemma roundup4k_facts : forall z, 0 <= z -> z <= roundup4k z < z + 4096 /\ roundup4k z mod 4096 = 0.
Proof.
  intros z Hz. unfold roundup4k. split; [|rewrite Z.mod_mul by lia; reflexivity].
  pose proof (Z.div_mod (z + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (z + 4095) 4096 ltac:(lia)). lia.
Qed.
Lemma roundup4k_id : forall z, z mod 4096 = 0 -> roundup4k z = z.
Proof. intros z Hz. unfold roundup4k. Z.div_mod_to_equations. nia. Qed.

(* [comment removed for export] *)
Definition hide (P : Prop) : Prop := P.

(* [comment removed for export] *)
Lemma find_segment_below : forall segs a, forallb (fun seg => a + 1 <=? Z.of_N (seg_base seg)) segs = true ->
  find_segment segs a 1 = None.
Proof.
  induction segs as [|seg segs IH]; intros a H; cbn in *; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1.
  rewrite (proj2 (Z.leb_gt (Z.of_N (seg_base seg)) a)) by lia. cbn [andb]. apply IH; assumption.
Qed.
Lemma asegs_bot : forallb (fun seg => img_hull_lo <=? Z.of_N (seg_base seg)) ctasegs = true.
Proof. vm_compute. reflexivity. Qed.
Lemma forallb_mono_bot : forall segs a b, a <= b ->
  forallb (fun seg => b <=? Z.of_N (seg_base seg)) segs = true -> forallb (fun seg => a <=? Z.of_N (seg_base seg)) segs = true.
Proof.
  induction segs as [|seg segs IH]; intros a b Hab H; cbn in *; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.leb_le in H1. rewrite (proj2 (Z.leb_le a _)) by lia. cbn [andb].
  apply (IH a b Hab H2).
Qed.
Lemma ro_free_low : forall x : word, bv_unsigned x < img_hull_lo -> ro_addr ctasegs x = false.
Proof.
  intros x Hx. unfold ro_addr. rewrite find_segment_below; [reflexivity|].
  apply (forallb_mono_bot ctasegs (bv_unsigned x + 1) img_hull_lo); [lia| exact asegs_bot].
Qed.
Lemma ro_free_out : forall x : word, bv_unsigned x < img_hull_lo \/ img_hull_hi <= bv_unsigned x -> ro_addr ctasegs x = false.
Proof. intros x [H|H]; [apply ro_free_low | apply ro_free_range]; exact H. Qed.

(* [comment removed for export] *)
Definition wmono_but (a e : Z) (m m' : mem) : Prop :=
  forall x : word, (bv_unsigned x < a \/ e <= bv_unsigned x) -> wview ctasegs m x <> None -> wview ctasegs m' x <> None.
Lemma wmono_but_of : forall a e m m', wmono ctasegs m m' -> wmono_but a e m m'.
Proof. intros a e m m' H x _ Hx. apply H, Hx. Qed.
Lemma wmono_but_trans_r : forall a e m1 m2 m3, wmono_but a e m1 m2 -> wmono ctasegs m2 m3 -> wmono_but a e m1 m3.
Proof. intros a e m1 m2 m3 H1 H2 x Hx Hw. apply H2, (H1 x Hx), Hw. Qed.
Lemma wmono_but_trans_l : forall a e m1 m2 m3, wmono ctasegs m1 m2 -> wmono_but a e m2 m3 -> wmono_but a e m1 m3.
Proof. intros a e m1 m2 m3 H1 H2 x Hx Hw. apply (H2 x Hx), H1, Hw. Qed.
Lemma wmono_but_unmaps : forall m a n, (0 <= a < 2^64) -> (0 <= n < 2^64) -> (a + n <= 2^64) ->
  wmono_but a (a + n) m (apply_unmaps m [(wa a, Z_to_bv 64 n)]).
Proof.
  intros m a n Ha Hn Han x Hx Hw. unfold wview in *.
  rewrite (unmaps_outside m a n Ha Hn Han x Hx). exact Hw.
Qed.
Lemma rw_cells_transport_but : forall W a e m m' A cs,
  rw_cells ctasegs m A cs -> munch W m m' -> wmono_but a e m m' ->
  disjoint_from W A (Z.of_nat (cells_size cs)) -> (A + Z.of_nat (cells_size cs) <= a \/ e <= A) ->
  rw_cells ctasegs m' A cs.
Proof.
  intros W a e m m' A cs [[Hwf Hb] Hw] Hm Hmono Hd Hout. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; eauto. rewrite cells_bytes_length by assumption. exact Hd.
  - destruct Hw as (H0 & H1 & H). split; [lia|]. split; [lia|]. intros i Hi. apply Hmono; [|apply H, Hi].
    rewrite wa_unsigned by lia. lia.
Qed.

(* [comment removed for export] *)
Ltac sys_mem_unmaps_but WB :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (apply_unmaps ?m [(?A, Z_to_bv 64 ?n)]) ?ro) =>
    let a := lazymatch A with wa ?a => a | Z_to_bv 64 ?a => a end in
    change (apply_unmaps m [(A, Z_to_bv 64 n)]) with (apply_unmaps m [(wa a, Z_to_bv 64 n)]);
    let Ha := fresh "Hua" in let Hn := fresh "Hun" in let Han := fresh "Huan" in
    assert (Ha : (0 <= a < 2^64)%Z) by lia;
    assert (Hn : (0 <= n < 2^64)%Z) by lia;
    assert (Han : (a + n <= 2^64)%Z) by lia;
    pose proof (wmono_but_unmaps m a n Ha Hn Han) as WB;
    transport_unmaps segs m a n Ha Hn Han;
    let m' := fresh "m" in
    set (m' := apply_unmaps m [(wa a, Z_to_bv 64 n)]) in *; clearbody m';
    clear Ha Hn Han
  end.

(* [comment removed for export] *)
Definition sec_page (m : mem) : Prop := rw_cells ctasegs m i_sec_page [C8 (Z_to_bv 64 4096)].
Definition sec_pad (m : mem) : Prop := rw_cells ctasegs m (i_sec_mutex + 1) [CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].

(* [comment removed for export] *)
Lemma sec_wr_at_app2 : forall segs m a n1 n2, (0 <= n1)%Z -> (0 <= n2)%Z ->
  wr_at segs m a (n1 + n2) <-> wr_at segs m a n1 /\ wr_at segs m (a + n1) n2.
Proof.
  intros segs m a n1 n2 H1 H2. unfold wr_at. split.
  - intros (Ha & Hb & H). repeat split; try lia.
    + intros i Hi. apply H. lia.
    + intros i Hi. replace (a + n1 + i)%Z with (a + (n1 + i))%Z by lia. apply H. lia.
  - intros ((Ha & Hb & HA) & (Ha' & Hb' & HB)). repeat split; try lia.
    intros i Hi. destruct (Z.lt_ge_cases i n1).
    + apply HA. lia.
    + replace (a + i)%Z with (a + n1 + (i - n1))%Z by lia. apply HB. lia.
Qed.
Lemma sec_rw_app2 : forall m A cs1 cs2,
  rw_cells ctasegs m A (cs1 ++ cs2) <-> rw_cells ctasegs m A cs1 /\ rw_cells ctasegs m (A + Z.of_nat (cells_size cs1)) cs2.
Proof.
  intros m A cs1 cs2. unfold rw_cells, cells_at.
  rewrite cells_wf_app, cells_bytes_app, cells_size_app, Nat2Z.inj_add.
  rewrite sec_wr_at_app2 by lia. rewrite bytes_at_app.
  split.
  - intros (((W1 & W2) & (B1 & B2)) & (R1 & R2)).
    rewrite (cells_bytes_length cs1 W1) in B2. tauto.
  - intros (((W1 & B1) & R1) & ((W2 & B2) & R2)).
    rewrite <- (cells_bytes_length cs1 W1) in B2. tauto.
Qed.
Lemma sec_relist : forall m A cs cs',
  rw_cells ctasegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> rw_cells ctasegs m A cs'.
Proof.
  intros m A cs cs' [[Hwf Hb] Hw] Hwf' E. split; [split; [exact Hwf'| rewrite E; exact Hb]|].
  rewrite <- (cells_bytes_length cs' Hwf'), E, (cells_bytes_length cs Hwf). exact Hw.
Qed.
Lemma sec_map_unsigned_inj : forall (l1 l2 : list byte), map (@bv_unsigned 8) l1 = map (@bv_unsigned 8) l2 -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. f_equal; [apply bv_eq; exact H1| apply IH; exact H2].
Qed.
Lemma sec_relistZ : forall m A cs cs',
  rw_cells ctasegs m A cs -> cells_wf cs' ->
  map (@bv_unsigned 8) (cells_bytes cs') = map (@bv_unsigned 8) (cells_bytes cs) -> rw_cells ctasegs m A cs'.
Proof. intros m A cs cs' H Hwf E. apply (sec_relist m A cs cs' H Hwf). apply sec_map_unsigned_inj. exact E. Qed.

(* [comment removed for export] *)
Lemma lockw_of : forall m, rw_cells ctasegs m i_sec_mutex [C1 (Z_to_bv 8 0)] -> sec_pad m ->
  rw_cells ctasegs m i_sec_mutex [C4 (Z_to_bv 64 0)].
Proof.
  intros m H1 H2. unfold sec_pad in H2.
  assert (H : rw_cells ctasegs m i_sec_mutex ([C1 (Z_to_bv 8 0)] ++ [CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]]))
    by (apply sec_rw_app2; split; [exact H1| exact H2]).
  eapply sec_relistZ; [exact H| vm_compute; repeat split; reflexivity| vm_compute; reflexivity].
Qed.
Lemma lockw_to1 : forall m, rw_cells ctasegs m i_sec_mutex [C4 (Z_to_bv 64 1)] ->
  rw_cells ctasegs m i_sec_mutex [C1 (Z_to_bv 8 1); CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]].
Proof. intros m H. eapply sec_relistZ; [exact H| vm_compute; repeat split; reflexivity| vm_compute; reflexivity]. Qed.
Lemma lockw_split : forall m (b : byte), rw_cells ctasegs m i_sec_mutex [C1 b; CB 3 [Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0]] ->
  rw_cells ctasegs m i_sec_mutex [C1 b] /\ sec_pad m.
Proof. intros m b H. apply (sec_rw_app2 m i_sec_mutex [C1 b] [CB 3 _]) in H. exact H. Qed.

(* [comment removed for export] *)
Definition i_sec_range : Z := INST + 0x50.
Definition i_sec_bylog : Z := INST + 0xa8.
Definition i_gstat_alloc : Z := INST + 0x2c0.
Definition sec_range (m : mem) (PAB : Z) : Prop := rw_cells ctasegs m i_sec_range [C8 (Z_to_bv 64 PAB)].
Definition sec_junk (m : mem) : Prop :=
  (exists (b : byte) (j : list byte) (w1 w2 w3 w4 : word), rw_cells ctasegs m i_sec_sorted [C1 b; CB 7 j; C8 w1; C8 w2; C8 w3; C8 w4])
  /\ (exists bl : list word, length bl = 64%nat /\ u64arr ctasegs m i_sec_bylog bl)
  /\ (exists ga gm : word, rw_cells ctasegs m i_gstat_alloc [C8 ga; C8 gm]).

(* [comment removed for export] *)
Definition sec_name : Z := 0x2eb3b.
Definition name_cells (m : mem) : Prop :=
  rw_cells ctasegs m 0x5a9220 [C8 (Z_to_bv 64 0x5ac4e8)] /\ rw_cells ctasegs m 0x5ac4e8 [C8 (Z_to_bv 64 sec_name)].

(* [comment removed for export] *)
Definition sa_msz (SZ : Z) : Z := roundup4k SZ + 4096.

(* [comment removed for export] *)
Definition gobj (b n lo : Z) : Prop :=
  0 < b /\ b + n <= lo /\ (b + n <= 0x7fff7000 \/ 0x10007fff8000 <= b) /\ (b + n <= img_hull_lo \/ img_hull_hi <= b).
Definition sapart (b1 n1 b2 n2 : Z) : Prop := b1 + n1 <= b2 \/ b2 + n2 <= b1.
