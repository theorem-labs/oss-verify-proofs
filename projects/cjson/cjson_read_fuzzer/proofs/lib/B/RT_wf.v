(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require Lia.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
Module ABand.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.

Section CeilWrap.
Context {ACEIL : Ceil}.

Definition ablk (lo hi : Z) : Prop :=
  (AIMG_HI <= lo /\ hi <= KLOWSHADOW_BEG) \/ (KHIGHMEM_BEG <= lo /\ hi <= alloc_ceiling).
Definition sclr (a n : Z) : Prop := a + n <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= a.
Definition iclr (a n : Z) : Prop := 4096 <= a /\ (a + n <= AIMG_LO \/ AIMG_HI <= a).

Lemma ablk_sub : forall lo hi lo' hi', ablk lo hi -> lo <= lo' -> hi' <= hi -> ablk lo' hi'.
Proof. intros lo hi lo' hi' H A B. unfold ablk in *. lia. Qed.

(* [comment removed for export] *)
Lemma ablk_lin : forall lo hi, ablk lo hi -> AIMG_HI <= lo /\ 0 <= lo /\ hi <= alloc_ceiling /\ hi + 8 <= 2^47.
Proof.
  intros lo hi H. pose proof alloc_ceiling_range as R. unfold ablk, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in *. lia.
Qed.
Lemma ablk_img : forall lo hi, ablk lo hi -> AIMG_HI <= lo.
Proof. intros lo hi H. apply ablk_lin in H. tauto. Qed.
Lemma ablk_top : forall lo hi, ablk lo hi -> hi <= alloc_ceiling.
Proof. intros lo hi H. apply ablk_lin in H. tauto. Qed.
Lemma ablk_high : forall lo hi, KHIGHMEM_BEG <= lo -> hi <= alloc_ceiling -> ablk lo hi.
Proof. intros lo hi A B. right. split; assumption. Qed.
Lemma ablk_low : forall lo hi, AIMG_HI <= lo -> hi <= KLOWSHADOW_BEG -> ablk lo hi.
Proof. intros lo hi A B. left. split; assumption. Qed.

Lemma ablk_sclr : forall lo hi, ablk lo hi -> sclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, sclr in *. lia. Qed.
Lemma ablk_iclr : forall lo hi, ablk lo hi -> iclr lo (hi - lo).
Proof. intros lo hi H. unfold ablk, iclr, AIMG_HI, AIMG_LO, KHIGHMEM_BEG in *. lia. Qed.

(* [comment removed for export] *)
Lemma ablk_clear_band : forall lo hi a, ablk lo hi -> KLOWSHADOW_BEG <= a < KHIGHMEM_BEG -> ~ (lo <= a < hi).
Proof. intros lo hi a H B. unfold ablk, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in *. lia. Qed.
Lemma ablk_disj_band : forall lo hi, ablk lo hi -> hi <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= lo.
Proof. intros lo hi H. unfold ablk in H. lia. Qed.

(* [comment removed for export] *)
Lemma ablk_shad : forall lo hi, ablk lo hi -> lo <= hi ->
  (SH AIMG_HI <= SH lo /\ SH hi <= SH KLOWSHADOW_BEG) \/ (SH KHIGHMEM_BEG <= SH lo /\ SH hi < KHIGHMEM_BEG).
Proof.
  intros lo hi H LE. pose proof alloc_ceiling_range as R.
  unfold ablk, SH, SHADOW_OFFSET, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in *.
  destruct H as [[A B]|[A B]]; [left|right]; split; try (apply Z.add_le_mono_l; apply Z.div_le_mono; lia).
  assert (hi / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; lia). change (0x7fffff800000 / 8) with 0xffffff00000 in H. lia.
Qed.

Lemma ablk_shad_lin : forall lo hi, ablk lo hi -> lo <= hi -> KLOWSHADOW_BEG < SH lo /\ SH hi < KHIGHMEM_BEG.
Proof.
  intros lo hi H LE. pose proof alloc_ceiling_range as R.
  assert (A1 : AIMG_HI / 8 <= lo / 8) by (apply Z.div_le_mono; [lia| apply ablk_img in H; exact H]).
  assert (A2 : hi / 8 <= 0x7fffff800000 / 8) by (apply Z.div_le_mono; [lia| apply ablk_top in H; lia]).
  unfold SH, SHADOW_OFFSET, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in *.
  change (0x5ff000 / 8) with 0xbfe00 in A1. change (0x7fffff800000 / 8) with 0xffffff00000 in A2. lia.
Qed.

(* [comment removed for export] *)
Lemma ablk_shad_disj : forall lo hi, ablk lo hi -> lo <= hi -> hi <= SH lo \/ SH (hi + 7) + 1 <= lo.
Proof.
  intros lo hi H LE. pose proof alloc_ceiling_range as R.
  unfold ablk, SH, SHADOW_OFFSET, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in *.
  destruct H as [[A B]|[A B]].
  - left. assert (0 <= lo / 8) by (apply Z.div_pos; lia). lia.
  - right. assert ((hi + 7) / 8 <= (0x7fffff800000 + 7) / 8) by (apply Z.div_le_mono; lia).
    change ((0x7fffff800000 + 7) / 8) with 0xffffff00000 in H. lia.
Qed.

(* [comment removed for export] *)
Definition oclr (lo hi : Z) : Prop := sclr lo (hi - lo) /\ iclr lo (hi - lo).

Lemma oclr_of_ablk : forall lo hi, ablk lo hi -> oclr lo hi.
Proof. intros lo hi H. split; [apply ablk_sclr| apply ablk_iclr]; exact H. Qed.

(* [comment removed for export] *)
Lemma oclr_ablk : forall lo hi, oclr lo hi -> 0x10000 <= hi - lo -> hi <= alloc_ceiling -> ablk lo hi.
Proof.
  intros lo hi [S I] Hn Hc. unfold sclr, iclr, ablk, AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in *.
  destruct I as [I0 [I|I]]; [lia|]. destruct S as [S|S]; [left|right]; lia.
Qed.

Lemma oclr_sub : forall lo hi lo' hi', oclr lo hi -> lo <= lo' -> lo' <= hi' -> hi' <= hi -> oclr lo' hi'.
Proof. intros lo hi lo' hi' [S I] A B C. unfold oclr, sclr, iclr in *. lia. Qed.

(* [comment removed for export] *)
Lemma oclr_lin : forall lo hi, oclr lo hi -> lo <= hi -> 4096 <= lo /\ (hi <= KLOWSHADOW_BEG \/ KHIGHMEM_BEG <= lo) /\ (hi <= AIMG_LO \/ AIMG_HI <= lo).
Proof. intros lo hi [S I] LE. unfold sclr, iclr in *. lia. Qed.

(* [comment removed for export] *)
Lemma oclr_not_img : forall lo hi a, oclr lo hi -> AIMG_LO <= a < AIMG_HI -> ~ (lo <= a < hi).
Proof. intros lo hi a [S I] B. unfold iclr in I. lia. Qed.
Lemma oclr_not_band : forall lo hi a, oclr lo hi -> KLOWSHADOW_BEG <= a < KHIGHMEM_BEG -> ~ (lo <= a < hi).
Proof. intros lo hi a [S I] B. unfold sclr in S. lia. Qed.

(* [comment removed for export] *)
Lemma oclr_of_disjoint : forall lo hi, 4096 <= lo -> lo < hi ->
  (hi <= AIMG_LO \/ AIMG_HI <= lo) ->
  (hi <= KLOWSHADOW_BEG \/ KLOWSHADOW_END <= lo) -> (hi <= KLOWSHADOW_END \/ KHIGHSHADOW_BEG <= lo) -> (hi <= KHIGHSHADOW_BEG \/ KHIGHMEM_BEG <= lo) ->
  oclr lo hi.
Proof.
  intros lo hi H0 H1 I S1 S2 S3. unfold oclr, sclr, iclr, KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG in *. lia.
Qed.

(* [comment removed for export] *)
Lemma ablk_below_stack : forall lo hi s, ablk lo hi -> alloc_ceiling <= s -> hi <= s.
Proof. intros lo hi s H S. apply ablk_top in H. lia. Qed.

End CeilWrap.

(* [comment removed for export] *)
Ltac blia := unfold ablk, oclr, sclr, iclr, AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KLOWSHADOW_END, KHIGHSHADOW_BEG, KHIGHMEM_BEG in *; lia.

(* [comment removed for export] *)
Goal forall {C : Ceil} lo hi x, ablk lo hi -> 0x5ff000 <= x < 0x5ff000 -> lo <= hi -> ~ (lo <= x < hi).
Proof. intros. blia. Qed.
Goal forall a b : Z, a < b -> a <= b.
Proof. intros. blia. Qed.
End ABand.

(* [comment removed for export] *)
Module RT_bandtac.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs ABand.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.

Ltac olin_core P lo hi :=
  let L := fresh "OL" in
  pose proof (oclr_lin lo hi P ltac:(lia)) as L;
  unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in L.
Ltac alin_core P lo hi :=
  let L := fresh "AL" in let D := fresh "AD" in
  pose proof (ablk_lin lo hi P) as L; pose proof (ablk_disj_band lo hi P) as D;
  unfold AIMG_LO, AIMG_HI, KLOWSHADOW_BEG, KHIGHMEM_BEG in L, D.
Ltac olin H :=
  lazymatch type of H with
  | oclr ?lo ?hi /\ _ => olin_core (proj1 H) lo hi
  | oclr ?lo ?hi => olin_core H lo hi
  | ablk ?lo ?hi /\ _ => alin_core (proj1 H) lo hi
  | ablk ?lo ?hi => alin_core H lo hi
  | ?T => fail "olin: not an oclr/ablk fact:" T
  end.
End RT_bandtac.

(* [comment removed for export] *)
Module RT_bandtac2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.micromega.Lia.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs ABand RT_bandtac.
Open Scope Z_scope.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.

Definition olin_done (lo hi : Z) : Prop := True.

Ltac olin_fresh lo hi := lazymatch goal with _ : olin_done lo hi |- _ => fail | _ => idtac end.
Ltac olin_mark lo hi := pose proof (I : olin_done lo hi).
Ltac olin_all :=
  repeat match goal with
  | H : oclr ?lo ?hi /\ _ |- _ => olin_fresh lo hi; olin_core (proj1 H) lo hi; olin_mark lo hi
  | H : oclr ?lo ?hi |- _ => olin_fresh lo hi; olin_core H lo hi; olin_mark lo hi
  | H : ablk ?lo ?hi /\ _ |- _ => olin_fresh lo hi; alin_core (proj1 H) lo hi; olin_mark lo hi
  | H : ablk ?lo ?hi |- _ => olin_fresh lo hi; alin_core H lo hi; olin_mark lo hi
  end.
End RT_bandtac2.

(* [comment removed for export] *)
From Stdlib Require List.
From Stdlib Require Bool.
Module RT_geom.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition nthz {A : Type} (l : list A) (i : Z) (d : A) : A :=
  if i <? 0 then d else nth (Z.to_nat i) l d.
Fixpoint updz_nat {A : Type} (l : list A) (i : nat) (x : A) : list A :=
  match l, i with
  | [], _ => []
  | _ :: l', O => x :: l'
  | y :: l', S i' => y :: updz_nat l' i' x
  end.
Definition updz {A : Type} (l : list A) (i : Z) (x : A) : list A :=
  if i <? 0 then l else updz_nat l (Z.to_nat i) x.
Definition zlen {A : Type} (l : list A) : Z := Z.of_nat (length l).
Definition zsum (l : list Z) : Z := fold_right Z.add 0 l.

Lemma nthz_updz_same : forall {A} (l : list A) i x d, 0 <= i < zlen l -> nthz (updz l i x) i d = x.
Proof.
  intros A l i x d Hi. unfold nthz, updz, zlen in *. destruct (Z.ltb_spec0 i 0) as [Hlt|Hge]; [lia|].
  remember (Z.to_nat i) as k eqn:Hk. assert (Hn : (k < length l)%nat) by lia. clear Hk Hi Hge i.
  revert k Hn. induction l as [|y l IH]; intros [|k] Hn; cbn in *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma nthz_updz_other : forall {A} (l : list A) i j x d, i <> j -> nthz (updz l i x) j d = nthz l j d.
Proof.
  intros A l i j x d Hij. unfold nthz, updz. destruct (Z.ltb_spec0 j 0) as [Hj|Hj]; [reflexivity|]. destruct (Z.ltb_spec0 i 0) as [Hi|Hi]; [reflexivity|].
  assert (Hn : Z.to_nat i <> Z.to_nat j) by lia. remember (Z.to_nat i) as a eqn:Ha. remember (Z.to_nat j) as b eqn:Hb. clear Ha Hb Hij Hi Hj i j.
  revert a b Hn. induction l as [|y l IH]; intros [|a] [|b] Hn; cbn; try reflexivity; try congruence. apply IH. congruence.
Qed.
Lemma updz_length : forall {A} (l : list A) i x, length (updz l i x) = length l.
Proof.
  intros A l i x. unfold updz. destruct (i <? 0); [reflexivity|]. remember (Z.to_nat i) as k eqn:Hk. clear Hk i.
  revert k. induction l as [|y l IH]; intros [|k]; cbn; try reflexivity. now rewrite IH.
Qed.
Lemma zlen_app : forall {A} (a b : list A), zlen (a ++ b) = zlen a + zlen b.
Proof. intros. unfold zlen. rewrite length_app. lia. Qed.
Lemma zlen_cons : forall {A} (x : A) l, zlen (x :: l) = 1 + zlen l.
Proof. intros. unfold zlen. cbn [length]. lia. Qed.
Lemma zlen_nil : forall {A}, zlen (@nil A) = 0.
Proof. reflexivity. Qed.
Lemma zlen_nonneg : forall {A} (l : list A), 0 <= zlen l.
Proof. intros. unfold zlen. lia. Qed.
Lemma zsum_app : forall a b, zsum (a ++ b) = zsum a + zsum b.
Proof. induction a; intros; cbn; [reflexivity|]. rewrite IHa. unfold zsum. cbn. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rg (st : rtstate) (c : Z) : region_st := nthz (st_regions st) c region0.
Definition cch (st : rtstate) (c : Z) : list Z := nthz (st_cache st) c [].
Definition rbeg (st : rtstate) (c : Z) : Z := region_beg (st_spacebeg st) c.        (* [comment removed for export] *)
Definition fabeg (st : rtstate) (c : Z) : Z := free_array (st_spacebeg st) c.        (* [comment removed for export] *)
Definition ris (st : rtstate) : Z := st_spacebeg st + KSPACESIZE.                    (* [comment removed for export] *)
Definition rinfo (st : rtstate) (c : Z) : Z := ris st + 128 * c.                      (* [comment removed for export] *)
Definition acache (st : rtstate) : Z := st_t st + T_ACACHE.                            (* [comment removed for export] *)
Definition pcaddr (st : rtstate) (c : Z) : Z := acache st + 80 * c.                   (* [comment removed for export] *)
Definition qcache_t (st : rtstate) : Z := st_t st + T_QCACHE.                          (* [comment removed for export] *)
Definition qcache_g : Z := A_QUAR + 160.                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Definition cptr_addr (st : rtstate) (c k : Z) : Z := rbeg st c + 16 * k.
Definition chunk_cptr (c j : Z) : Z := j * csize c / 16.
Definition ncarved (st : rtstate) (c : Z) : Z := r_allocated (rg st c) / csize c.   (* [comment removed for export] *)
Definition num_freed (st : rtstate) (c : Z) : Z := zlen (r_fa (rg st c)).
(* [comment removed for export] *)
Definition emb_d (st : rtstate) : Z := tl_emb_d (st_tls st).
Definition emb_sz (st : rtstate) : Z := tl_emb_sz (st_tls st).
(* [comment removed for export] *)
Fixpoint count_exh (l : list region_st) : Z :=
  match l with [] => 0 | r :: l' => (if r_exhausted r then 1 else 0) + count_exh l' end.
Definition nexh (st : rtstate) : Z := count_exh (st_regions st).
Lemma count_exh_bound : forall l, 0 <= count_exh l <= zlen l.
Proof. induction l as [|r l IH]; [cbn; unfold zlen; cbn; lia|]. cbn [count_exh]. unfold zlen in *. cbn [length]. rewrite Nat2Z.inj_succ. destruct (r_exhausted r); lia. Qed.
Lemma count_exh_app : forall l1 l2, count_exh (l1 ++ l2) = count_exh l1 + count_exh l2.
Proof. induction l1 as [|r l1 IH]; intros l2; cbn; [reflexivity|]. rewrite IH. lia. Qed.
Lemma count_exh_updz_nat : forall l i x, (i < length l)%nat ->
  count_exh (updz_nat l i x) = count_exh l - (if r_exhausted (nth i l region0) then 1 else 0) + (if r_exhausted x then 1 else 0).
Proof.
  induction l as [|r l IH]; intros [|i] x Hi; cbn in *; try lia.
  rewrite (IH i x) by lia. lia.
Qed.
Lemma count_exh_updz : forall l i x, 0 <= i < zlen l ->
  count_exh (updz l i x) = count_exh l - (if r_exhausted (nthz l i region0) then 1 else 0) + (if r_exhausted x then 1 else 0).
Proof.
  intros l i x Hi. unfold updz, nthz, zlen in *. destruct (Z.ltb_spec0 i 0); [lia|]. apply count_exh_updz_nat. lia.
Qed.
Lemma nexh_bound : forall st, length (st_regions st) = 32%nat -> 0 <= nexh st <= 32.
Proof. intros st L. unfold nexh. pose proof (count_exh_bound (st_regions st)) as B. unfold zlen in B. rewrite L in B. cbn in B. lia. Qed.
(* [comment removed for export] *)
Definition dtls_same (st st' : rtstate) : Prop :=
  tl_dtls_block (st_tls st') = tl_dtls_block (st_tls st) /\ tl_dtls_w (st_tls st') = tl_dtls_w (st_tls st).
Definition loose0_ext (st st' : rtstate) : Prop := exists l, st_loose0 st' = st_loose0 st ++ l.
Lemma dtls_same_refl : forall st, dtls_same st st.             Proof. intros; split; reflexivity. Qed.
Lemma loose0_ext_refl : forall st, loose0_ext st st.           Proof. intros; exists []; symmetry; apply app_nil_r. Qed.
Lemma dtls_same_of_eq : forall st st', st_tls st' = st_tls st -> dtls_same st st'.
Proof. intros st st' E. unfold dtls_same. rewrite E. split; reflexivity. Qed.
Lemma loose0_ext_of_eq : forall st st', st_loose0 st' = st_loose0 st -> loose0_ext st st'.
Proof. intros st st' E. exists []. rewrite E, app_nil_r. reflexivity. Qed.
Lemma loose0_ext_trans : forall st1 st2 st3, loose0_ext st1 st2 -> loose0_ext st2 st3 -> loose0_ext st1 st3.
Proof. intros st1 st2 st3 [l1 E1] [l2 E2]. exists (l1 ++ l2). rewrite E2, E1, app_assoc. reflexivity. Qed.
Lemma loose0_ext_In : forall st st' e, loose0_ext st st' -> In e (st_loose0 st) -> In e (st_loose0 st').
Proof. intros st st' e [l E] H. rewrite E. apply in_or_app. left. exact H. Qed.
(* [comment removed for export] *)
Definition fresh_cls (st : rtstate) (c : Z) : Prop := rg st c = region0 /\ cch st c = [].
Definition fa_cap (st : rtstate) (c : Z) : Z := r_mapped_fa (rg st c) / 4.            (* [comment removed for export] *)
(* [comment removed for export] *)
Definition carved_cptr (st : rtstate) (c k : Z) : Prop :=
  exists j, 0 <= j < ncarved st c /\ k = chunk_cptr c j.
(* [comment removed for export] *)
Definition nrefill (c : Z) : Z := cmaxcount c / 2.
Definition pc_max_count (st : rtstate) (c : Z) : Z := if st_cache_inited st && negb (c =? 0) then cmaxcount c else 0.
Definition pc_class_size (st : rtstate) (c : Z) : Z := if st_cache_inited st && negb (c =? 0) then csize c else 0.
(* [comment removed for export] *)
Fixpoint index_of (l : list (Z * Z)) (mb : Z) : Z :=
  match l with [] => 0 | e :: l' => if fst e =? mb then 0 else 1 + index_of l' mb end.
Definition sec_index (st : rtstate) (mb : Z) : Z := index_of (st_sec st) mb.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bprim (n : Z) : bool := is_primary n.
Definition b_alloc_beg (A n : Z) : Z := A - rz_size n.                 (* [comment removed for export] *)
Definition b_chunk_beg (A : Z) : Z := A - 16.                          (* [comment removed for export] *)
Definition b_alloc_size (n : Z) : Z := asz n.                          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition SEC_HDR : Z := 4096.  Definition SEC_RZ : Z := 2048.
Definition b_map_beg (A : Z) : Z := A - SEC_RZ - SEC_HDR.
Definition sec_user (mb : Z) : Z := mb + SEC_HDR + SEC_RZ.
Definition sec_alloc_beg (mb : Z) : Z := mb + SEC_HDR.
(* [comment removed for export] *)
Definition b_class (n : Z) : Z := pclass n.
Definition b_cptr (st : rtstate) (A n : Z) : Z := (b_alloc_beg A n - rbeg st (pclass n)) / 16.
(* [comment removed for export] *)
Definition b_lo (A n : Z) : Z := if bprim n then b_alloc_beg A n else b_map_beg A.
Definition b_hi (A n : Z) : Z := b_lo A n + asz n.
(* [comment removed for export] *)
Definition hdr_state_live : Z := CHUNK_ALLOCATED.
Definition hdr_state_quar : Z := CHUNK_QUARANTINE.
Definition hdr_b1_ok (b : Z) : Prop := Z.land b 127 = HDR_BYTE1_MALLOC.   (* [comment removed for export] *)
Definition size_hi (n : Z) : Z := usz n / 2^32.
Definition size_lo (n : Z) : Z := usz n mod 2^32.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zrep (v : Z) (k : Z) : list Z := repeat v (Z.to_nat k).
(* [comment removed for export] *)
Definition sh_chunk (left tot : Z) (mid : list Z) : list Z :=
  zrep SV_HEAP_LEFT_RZ left ++ mid ++ zrep SV_HEAP_LEFT_RZ (tot - left - zlen mid).
Definition sh_left (n : Z) : Z := if bprim n then rz_size n / 8 else (SEC_HDR + SEC_RZ) / 8.
Definition sh_tot (n : Z) : Z := asz n / 8.
Definition sh_live (n : Z) : list Z := sh_chunk (sh_left n) (sh_tot n) (shadow_enc (usz n)).
Definition sh_quar (n : Z) : list Z := sh_chunk (sh_left n) (sh_tot n) (zrep SV_HEAP_FREED (zlen (shadow_enc (usz n)))).
Definition sh_avail (c : Z) : list Z := zrep SV_HEAP_LEFT_RZ (csize c / 8).
(* [comment removed for export] *)
Definition b_sh_lo (A n : Z) : Z := SH (b_lo A n).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition qall (st : rtstate) : list qbatch := st_qthread st ++ st_qglobal st ++ st_qtmp st ++ map fst (st_qcur st).
(* [comment removed for export] *)
Definition qelems (st : rtstate) : list (Z * Z) :=
  flat_map qb_elems (st_qthread st ++ st_qglobal st ++ st_qtmp st)
  ++ flat_map (fun bd : qbatch * Z => skipn (Z.to_nat (snd bd)) (qb_elems (fst bd))) (st_qcur st).
Definition qbatch_addrs (st : rtstate) : list Z := map qb_addr (qall st).
(* [comment removed for export] *)
Definition qc_first (q : list qbatch) : Z := match q with [] => 0 | b :: _ => qb_addr b end.
Definition qc_last (q : list qbatch) : Z := match q with [] => 0 | _ => qb_addr (last q (mkQB 0 [])) end.
Fixpoint qb_nexts (q : list qbatch) : list (Z * Z) :=      (* [comment removed for export] *)
  match q with
  | [] => []
  | b :: q' => (qb_addr b, qc_first q') :: qb_nexts q'
  end.
Definition thread_room (st : rtstate) : Z :=               (* [comment removed for export] *)
  match st_qthread st with [] => 0 | _ => QBATCH_CAP - qb_count (last (st_qthread st) (mkQB 0 [])) end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition dnode (d : depot_st) (id : Z) : Z * Z * Z := nthz (d_nodes d) (id - 1) (0, 0, 0).
Definition dn_hash (x : Z * Z * Z) : Z := fst (fst x).
Definition dn_link (x : Z * Z * Z) : Z := snd (fst x).
Definition dn_store (x : Z * Z * Z) : Z := snd x.
Definition dnode_addr (d : depot_st) (id : Z) : Z := nthz (d_nblocks d) (id / DEPOT_L2_NODES) 0 + DEPOT_NODE_SZ * (id mod DEPOT_L2_NODES).
Definition d_nnb (d : depot_st) : Z := zlen (d_nblocks d).
Definition d_nsb (d : depot_st) : Z := zlen (d_sblocks d).
Definition dbucket (h : Z) : Z := h mod 2^DEPOT_TAB_LOG.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fhint (st : rtstate) (k : Z) : Z := nthz (st_hints st) k 0.
(* [comment removed for export] *)
Definition fpos (st : rtstate) (F k : Z) : Z := (F - (st_fs st + FS_FRAMES_OFF + Z.shiftl 1 FS_LOG * k)) / fsz k.
Definition flag_live (st : rtstate) (k pos : Z) : bool :=
  existsb (fun fk => (snd fk =? k) && (fst fk =? fframe_addr (st_fs st) k pos)) (st_lf st).
Definition flag_val (st : rtstate) (k pos : Z) : Z := if flag_live st k pos then 1 else 0.
Definition lf_of_class (st : rtstate) (k : Z) : list Z := map fst (filter (fun fk => snd fk =? k) (st_lf st)).

(* [comment removed for export] *)
Definition A_VERBOSITY : Z := 0x139458.        (* [comment removed for export] *)
Definition A_TLSMOD : Z := 1.                  (* [comment removed for export] *)
Definition A_TLSOFF : Z := 0xfffffffffffff800. (* [comment removed for export] *)
Definition A_DTLS_OFF : Z := 8.   (* [comment removed for export] *)             (* [comment removed for export] *)
Definition HIGHSHADOW_SIZE : Z := KHIGHMEM_BEG - KHIGHSHADOW_BEG.
Definition LOWSHADOW_SIZE : Z := KLOWSHADOW_END - KLOWSHADOW_BEG.
Lemma fstls_cell_ok : (A_TLSBASE + A_TLSOFF) mod 2^64 = A_FSTLS_CELL.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lb_prim (st : rtstate) (c : Z) : list (Z * Z) := filter (fun b => bprim (snd b) && (pclass (snd b) =? c)) (st_lb st).
Definition lb_sec (st : rtstate) : list (Z * Z) := filter (fun b => negb (bprim (snd b))) (st_lb st).
Definition q_prim (st : rtstate) (c : Z) : list (Z * Z) := filter (fun b => bprim (snd b) && (pclass (snd b) =? c)) (qelems st).
Definition q_sec (st : rtstate) : list (Z * Z) := filter (fun b => negb (bprim (snd b))) (qelems st).
Definition avail_cptrs (st : rtstate) (c : Z) : list Z := r_fa (rg st c) ++ cch st c.
Definition live_cptrs (st : rtstate) (c : Z) : list Z := map (fun b => b_cptr st (fst b) (snd b)) (lb_prim st c).
Definition quar_cptrs (st : rtstate) (c : Z) : list Z := map (fun b => b_cptr st (fst b) (snd b)) (q_prim st c).
Definition batch_cptrs (st : rtstate) (c : Z) : list Z :=
  if c =? 24 then map (fun a => (a - rbeg st 24) / 16) (qbatch_addrs st) else [].
(* [comment removed for export] *)
Definition qp_prim (st : rtstate) (c : Z) : list (Z * Z) := filter (fun b => bprim (snd b) && (pclass (snd b) =? c)) (st_qpend st).
Definition qpend_cptrs (st : rtstate) (c : Z) : list Z := map (fun b => b_cptr st (fst b) (snd b)) (qp_prim st c).
Definition apend_cptrs (st : rtstate) (c : Z) : list Z := map snd (filter (fun ck => fst ck =? c) (st_apend st)).
(* [comment removed for export] *)
Definition used_cptrs (st : rtstate) (c : Z) : list Z :=
  avail_cptrs st c ++ live_cptrs st c ++ quar_cptrs st c ++ qpend_cptrs st c ++ batch_cptrs st c ++ apend_cptrs st c.
(* [comment removed for export] *)
Definition blk_cptrs (st : rtstate) (c : Z) : list Z := live_cptrs st c ++ quar_cptrs st c ++ qpend_cptrs st c.
Lemma used_cptrs_split : forall st c,
  used_cptrs st c = avail_cptrs st c ++ blk_cptrs st c ++ (batch_cptrs st c ++ apend_cptrs st c).
Proof. intros. unfold used_cptrs, blk_cptrs. rewrite <- !app_assoc. reflexivity. Qed.
Definition navail (st : rtstate) (c : Z) : Z := zlen (avail_cptrs st c).
(* [comment removed for export] *)
Definition sec_users (st : rtstate) : list Z := map (fun e => sec_user (fst e)) (st_sec st).
Definition nsec (st : rtstate) : Z := zlen (st_sec st).


End CeilWrap.
End RT_geom.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_defs.
Import RT_geom.
Import ABand.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint pwdj (L : list (Z * Z)) : Prop :=
  match L with
  | [] => True
  | r :: L' => Forall (fun r' => snd r <= fst r' \/ snd r' <= fst r) L' /\ pwdj L'
  end.

Lemma pwdj_In : forall L r1 r2, pwdj L -> In r1 L -> In r2 L -> r1 = r2 \/ snd r1 <= fst r2 \/ snd r2 <= fst r1.
Proof.
  induction L as [|r L IH]; intros r1 r2 HP H1 H2; [destruct H1|].
  cbn in HP. destruct HP as [HF HP]. destruct H1 as [<-|H1], H2 as [<-|H2].
  - left; reflexivity.
  - right. rewrite Forall_forall in HF. specialize (HF r2 H2). lia.
  - right. rewrite Forall_forall in HF. specialize (HF r1 H1). lia.
  - apply IH; assumption.
Qed.

Lemma pwdj_cons : forall r L, pwdj (r :: L) <-> (Forall (fun r' => snd r <= fst r' \/ snd r' <= fst r) L /\ pwdj L).
Proof. intros. cbn. tauto. Qed.

Lemma pwdj_app_comm : forall r L1 L2, pwdj (L1 ++ r :: L2) -> pwdj (r :: L1 ++ L2).
Proof.
  intros r L1 L2. revert r L2. induction L1 as [|x L1 IH]; intros r L2 H; [exact H|].
  cbn in H. destruct H as [HF HP]. apply IH in HP. cbn in HP. destruct HP as [HF2 HP2].
  cbn. split; [|split].
  - constructor.
    + apply Forall_app in HF as [_ HF]. inversion HF; subst. lia.
    + exact HF2.
  - apply Forall_app in HF as [HA HB]. inversion HB; subst. apply Forall_app. split; assumption.
  - exact HP2.
Qed.

(* [comment removed for export] *)
Definition nodupZ (l : list Z) : Prop := NoDup l.

Lemma NoDup_incl_length_Z : forall (l : list Z) (n : Z),
  NoDup l -> (forall x, In x l -> 0 <= x < n) -> zlen l <= Z.max n 0.
Proof.
  intros l n Hnd Hr. unfold zlen.
  destruct (Z_lt_le_dec n 0) as [Hn|Hn].
  { destruct l as [|x l]; [cbn; lia|]. exfalso. pose proof (Hr x (or_introl eq_refl)). lia. }
  rewrite Z.max_l by lia.
  assert (Hincl : incl l (map Z.of_nat (seq 0 (Z.to_nat n)))).
  { intros x Hx. apply in_map_iff. exists (Z.to_nat x). pose proof (Hr x Hx). split; [lia|]. apply in_seq. lia. }
  pose proof (NoDup_incl_length Hnd Hincl) as HL. rewrite length_map, length_seq in HL. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MM_M : Z := 0xc6a4a7935bd1e995.
Definition MM_SEED : Z := 0x9747b28c9747b28c.
Definition w64 (z : Z) : Z := z mod 2^64.
Definition mm_add (h w : Z) : Z :=
  let k := w64 (w * MM_M) in
  let k := Z.lxor k (Z.shiftr k 47) in
  let k := w64 (k * MM_M) in
  w64 (Z.lxor h k * MM_M).
Definition mm_fin (h : Z) : Z :=
  let h := Z.lxor h (Z.shiftr h 47) in
  let h := w64 (h * MM_M) in
  Z.lxor h (Z.shiftr h 47).
Definition murmur64 (tr : list Z) : Z :=
  mm_fin (mm_add (fold_left mm_add tr (Z.lxor MM_SEED (w64 (8 * zlen tr * MM_M)))) 0).
(* [comment removed for export] *)
Definition trace_hash (tr : list Z) : Z := murmur64 tr.

(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive dreach (d : depot_st) (b : Z) : Z -> Prop :=
| dreach_head : forall id, d_tab d b = id -> id <> 0 -> dreach d b id
| dreach_link : forall id id', dreach d b id' -> dn_link (dnode d id') = id -> id <> 0 -> dreach d b id.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition rt_ranges (st : rtstate) : list (Z * Z) :=
  (st_pbase st, st_pbase st + PRIM_RES_SIZE)
  :: (st_pa st, st_pa st + PTRARR_RES_SIZE)
  :: map (fun e => (fst e, fst e + snd e)) (st_loose0 st)
  ++ map (fun e => (fst e, fst e + smapsize (snd e))) (st_sec st)
  ++ map (fun b => (b, b + NODEBLOCK_SIZE)) (d_nblocks (st_depot st))
  ++ map (fun b => (b, b + STOREBLOCK_SIZE)) (d_sblocks (st_depot st)).

(* [comment removed for export] *)
Definition in_loose0 (st : rtstate) (lo hi : Z) : Prop :=
  exists b k, In (b, k) (st_loose0 st) /\ b <= lo /\ hi <= b + k.

(* [comment removed for export] *)
Definition all_blocks (st : rtstate) : list (Z * Z) := st_lb st ++ qelems st ++ st_qpend st.

Section WF.
Variable st : rtstate.
Let S := st_spacebeg st.
Let P := st_pbase st.
Let d := st_depot st.

(* [comment removed for export] *)
Record wf_base : Prop := mkWFB {
  wb_len_regions : length (st_regions st) = 32%nat;
  wb_len_cache : length (st_cache st) = 32%nat;
  wb_len_hints : length (st_hints st) = 11%nat;
  wb_S_align : S mod 65536 = 0;    (* [comment removed for export] *)
  wb_P_align : P mod 4096 = 0;
  wb_P_S : P <= S /\ S + KSPACESIZE + 4096 <= P + PRIM_RES_SIZE;
  wb_pa_align : st_pa st mod 4096 = 0;
  wb_t_align : st_t st mod 4096 = 0;
  wb_fs_align : st_fs st mod 4096 = 0;
  wb_ranges : forall r, In r (rt_ranges st) -> oclr (fst r) (snd r) /\ fst r < snd r /\ snd r <= alloc_ceiling /\ fst r mod 4096 = 0;   (* [comment removed for export] *)
  wb_pwdj : pwdj (rt_ranges st);
  wb_t_loose : In (st_t st, 4096) (st_loose0 st);
  wb_fs_loose : In (st_fs st, FS_TOTAL) (st_loose0 st);
  wb_ctx_loose : in_loose0 st (st_ctx st) (st_ctx st + 160);
  wb_ctx_fs : st_ctx st + 160 <= st_fs st \/ st_fs st + FS_TOTAL <= st_ctx st;
  wb_dtls_loose : in_loose0 st (tl_dtls_block (st_tls st) + 24) (tl_dtls_block (st_tls st) + 32);
  wb_dtls_fs : tl_dtls_block (st_tls st) + 32 <= st_fs st \/ st_fs st + FS_TOTAL <= tl_dtls_block (st_tls st) + 24;
  wb_ctx_t : st_ctx st + 160 <= st_t st \/ st_t st + 4096 <= st_ctx st;                                   (* [comment removed for export] *)
  wb_dtls_t : tl_dtls_block (st_tls st) + 32 <= st_t st \/ st_t st + 4096 <= tl_dtls_block (st_tls st) + 24;  (* [comment removed for export] *)
  wb_dtls_w : 0 < tl_dtls_w (st_tls st) < 2^64;
  wb_sp0 : 0x7fff80000000 <= st_sp0 st /\ st_sp0 st + 192 <= 2^47 /\ st_sp0 st mod 16 = 0;   (* [comment removed for export] *)
  wb_nres : 0 <= st_nreserved st /\ st_nreserved st mod 2^14 = 0 /\ 8 * st_nreserved st <= PTRARR_RES_SIZE;
  wb_class0 : rg st 0 = region0 /\ cch st 0 = [];
  wb_uninit : st_cache_inited st = false -> forall c, cch st c = [];
  wb_hints : forall k, 0 <= fhint st k;
  (* [comment removed for export] *)
  wb_emb_loose : emb_d st <> 0 -> In (emb_d st, EMB_CAP) (st_loose0 st);
  wb_emb_ctx : emb_d st <> 0 -> st_ctx st + 160 <= emb_d st \/ emb_d st + EMB_CAP <= st_ctx st;
  wb_emb_dtls : emb_d st <> 0 -> tl_dtls_block (st_tls st) + 32 <= emb_d st \/ emb_d st + EMB_CAP <= tl_dtls_block (st_tls st) + 24;
  wb_emb_sz : 0 <= emb_sz st <= EMB_MSG * nexh st;
  wb_emb_d0 : emb_d st = 0 -> emb_sz st = 0 }.

(* [comment removed for export] *)
Record wf_class (c : Z) : Prop := mkWFC {
  wc_alloc_nonneg : 0 <= r_allocated (rg st c);
  wc_alloc_carved : r_allocated (rg st c) = ncarved st c * csize c;
  wc_alloc_mapped : r_allocated (rg st c) <= r_mapped (rg st c);
  wc_mapped_align : r_mapped (rg st c) mod 2^18 = 0;
  wc_mapped_max : r_mapped (rg st c) <= KFREEARRAY_OFF;
  wc_fa_nonneg : 0 <= r_mapped_fa (rg st c);
  wc_fa_align : r_mapped_fa (rg st c) mod 2^18 = 0;
  wc_fa_max : r_mapped_fa (rg st c) <= KFREEARRAY_SIZE;
  wc_num_freed : 4 * num_freed st c <= r_mapped_fa (rg st c);
  wc_cache_max : zlen (cch st c) <= cmaxcount c;
  (* [comment removed for export] *)
  wc_used_carved : forall k, In k (used_cptrs st c) -> carved_cptr st c k;
  wc_used_nodup : NoDup (used_cptrs st c);
  wc_used_all : zlen (used_cptrs st c) = ncarved st c;
  (* [comment removed for export] *)
  wc_residue : r_mapped (rg st c) <= r_allocated (rg st c) + csize c + 2^18;
  (* [comment removed for export] *)
  wc_delta : 1 <= c -> r_mapped (rg st c) < r_allocated (rg st c) + csize c
                       \/ (r_allocated (rg st c) + 2^18 <= r_mapped (rg st c) /\ r_mapped (rg st c) < r_allocated (rg st c) + 2^18 + csize c);
  wc_exh : r_exhausted (rg st c) = true -> r_mapped (rg st c) = KFREEARRAY_OFF /\ r_mapped (rg st c) < r_allocated (rg st c) + csize c }.

(* [comment removed for export] *)
Definition wf_block (b : Z * Z) : Prop :=
  let A := fst b in let n := snd b in
  0 <= n < 2^40 /\ A mod 16 = 0
  /\ (bprim n = true ->
        1 <= pclass n <= 30
        /\ 0 <= b_cptr st A n /\ b_alloc_beg A n = cptr_addr st (pclass n) (b_cptr st A n))
  /\ (bprim n = false -> In (b_map_beg A, n) (st_sec st)).
Record wf_blocks : Prop := mkWFK {
  wk_block : forall b, In b (all_blocks st) -> wf_block b;
  wk_nodup : NoDup (map fst (all_blocks st)) }.

(* [comment removed for export] *)
Record wf_sec : Prop := mkWFS {
  ws_nodup : NoDup (map fst (st_sec st));
  ws_nres : nsec st <= st_nreserved st;
  ws_entry : forall e, In e (st_sec st) ->
        bprim (snd e) = false /\ 0 <= snd e < 2^40 /\ fst e mod 4096 = 0
        /\ (In (sec_user (fst e), snd e) (all_blocks st) \/ In e (st_spend st));
  ws_spend : forall e, In e (st_spend st) -> In e (st_sec st) /\ ~ In (sec_user (fst e), snd e) (all_blocks st);
  ws_spend_nodup : NoDup (st_spend st) }.

(* [comment removed for export] *)
Record wf_quar : Prop := mkWFQ {
  wq_batch : forall b, In b (qall st) -> qb_count b <= QBATCH_CAP /\ exists k, carved_cptr st 24 k /\ qb_addr b = cptr_addr st 24 k;
  wq_thread_nonempty : forall b, In b (st_qthread st) -> 1 <= qb_count b;
  (* [comment removed for export] *)
  wq_thread_max : qc_bytes (st_qthread st) <= QUAR_MAX_CACHE;
  wq_global_max : qc_bytes (st_qglobal st) <= QUAR_MAX_SIZE;
  wq_rec_max : qc_bytes (st_qglobal st) + qc_bytes (st_qtmp st) + qc_bytes (map fst (st_qcur st)) <= 2 * QUAR_MAX_SIZE + QUAR_MAX_CACHE + QBATCH_SIZE;
  (* [comment removed for export] *)
  wq_inflight : zlen (st_apend st) <= 1 /\ zlen (st_qpend st) <= 1;
  wq_cur : forall bd, In bd (st_qcur st) -> 0 <= snd bd <= qb_count (fst bd);
  wq_apend : forall ck, In ck (st_apend st) -> 1 <= fst ck < KNUMCLASSES }.

(* [comment removed for export] *)
Record wf_depot : Prop := mkWFD {
  wd_node : forall id, 1 <= id <= d_U d ->
      0 <= dn_link (dnode d id) < id /\ 0 <= dn_hash (dnode d id) < 2^64 /\ 0 <= dn_store (dnode d id) < 2^32;
  wd_tab : forall b, 0 <= b < 2^DEPOT_TAB_LOG -> d_tab d b = 0 \/ 1 <= d_tab d b <= d_U d;
  wd_tab_out : forall b, ~ (0 <= b < 2^DEPOT_TAB_LOG) -> d_tab d b = 0;
  wd_reach_sound : forall b id, dreach d b id -> 1 <= id <= d_U d /\ dbucket (dn_hash (dnode d id)) = b;
  wd_reach_complete : forall id, 1 <= id <= d_U d -> dreach d (dbucket (dn_hash (dnode d id))) id;
  wd_traces : forall tr, In tr (st_trs st ++ st_trs0 st) -> exists id, 1 <= id <= d_U d /\ dn_hash (dnode d id) = trace_hash tr;
  wd_U_le : d_U d <= zlen (st_trs st) + zlen (st_trs0 st);
  wd_trs0 : zlen (st_trs0 st) <= 1;
  wd_trs_max : zlen (st_trs st) <= DEPOT_KMAX;
  wd_U_pos : 1 <= d_U d;
  wd_nnb : d_nnb d = d_U d / DEPOT_L2_NODES + 1;           (* [comment removed for export] *)
  wd_nnb_max : d_nnb d <= DEPOT_NNB_MAX;
  wd_T_pos : 1 <= d_T d;
  wd_T_le : d_T d <= 31 * (zlen (st_trs st) + 1) + 31 * d_nsb d;
  wd_nsb : d_nsb d = (d_T d - 1) / SSTORE_BLOCK_FRAMES + 1;
  wd_nsb_max : d_nsb d <= DEPOT_NSB_MAX;
  wd_nb_align : forall b, In b (d_nblocks d) -> b mod 4096 = 0;
  wd_sb_align : forall b, In b (d_sblocks d) -> b mod 4096 = 0 }.

(* [comment removed for export] *)
Record wf_fs : Prop := mkWFF {
  wff_nodup : NoDup (map fst (st_lf st));
  wff_frame : forall F k, In (F, k) (st_lf st) ->
        (k = 1 \/ k = 2) /\ 0 <= fpos st F k < fcap k /\ F = fframe_addr (st_fs st) k (fpos st F k) }.

Record RTWF : Prop := mkRTWF {
  wf_base_ok : wf_base;
  wf_class_ok : forall c, 0 <= c < KNUMCLASSES -> wf_class c;
  wf_blocks_ok : wf_blocks;
  wf_sec_ok : wf_sec;
  wf_quar_ok : wf_quar;
  wf_depot_ok : wf_depot;
  wf_fs_ok : wf_fs }.
End WF.

(* [comment removed for export] *)
Lemma RTWF_pd : forall st c, RTWF st -> 1 <= c < KNUMCLASSES ->
  (r_mapped (rg st c) < r_allocated (rg st c) + csize c
   \/ (r_allocated (rg st c) + 2^18 <= r_mapped (rg st c) /\ r_mapped (rg st c) < r_allocated (rg st c) + 2^18 + csize c))
  /\ (r_exhausted (rg st c) = true -> r_mapped (rg st c) = KFREEARRAY_OFF /\ r_mapped (rg st c) < r_allocated (rg st c) + csize c).
Proof.
  intros st c WF Hc. pose proof (wf_class_ok st WF c ltac:(lia)) as WC. split; [apply (wc_delta st c WC); lia| exact (wc_exh st c WC)].
Qed.

(* [comment removed for export] *)
Lemma emb_block_range : forall st, RTWF st -> emb_d st <> 0 ->
  ablk (emb_d st) (emb_d st + EMB_CAP) /\ emb_d st + EMB_CAP <= alloc_ceiling /\ emb_d st mod 4096 = 0.
Proof.
  intros st WF Hd. pose proof (wb_ranges st (wf_base_ok st WF) (emb_d st, emb_d st + EMB_CAP)) as R. cbn [fst snd] in R.
  assert (In (emb_d st, emb_d st + EMB_CAP) (rt_ranges st)).
  { unfold rt_ranges. do 2 right. rewrite !in_app_iff. left. apply in_map_iff. exists (emb_d st, EMB_CAP).
    split; [reflexivity| apply (wb_emb_loose st (wf_base_ok st WF)); exact Hd]. }
  specialize (R H). destruct R as (R1 & R2 & R3 & R4). split; [apply oclr_ablk; [exact R1| unfold EMB_CAP; lia| exact R3]| split; [exact R3| exact R4]].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition LUMPU : Z := 2^18 + 2^15.        (* [comment removed for export] *)
Definition LUMPF : Z := LUMPU.
Definition FAPROV : Z := 8.                 (* [comment removed for export] *)
Definition Nmax (c : Z) : Z := 2^18 / csize c + 256. (* [comment removed for export] *)
Definition delta (st : rtstate) (c : Z) : Z := r_mapped (rg st c) - r_allocated (rg st c).
Definition provU (st : rtstate) (c : Z) : Z :=
  Z.max 0 ((if delta st c <? nrefill c * csize c then LUMPU else 0) + FAPROV * Nmax c - 2 * csize c * navail st c).
Definition provF (st : rtstate) (c : Z) : Z :=
  Z.max 0 (LUMPF - FAPROV * (fa_cap st c - ncarved st c)).
Definition classes : list Z := map Z.of_nat (seq 1 31).
Definition prov_classes (st : rtstate) : Z := zsum (map (fun c => provU st c + provF st c) classes).
Definition NB : Z := 16640.                 (* [comment removed for export] *)
Definition SLOTP : Z := 18.                 (* [comment removed for export] *)
Definition prov_nb (st : rtstate) : Z :=
  match st_qthread st with [] => NB | _ => Z.max 0 (NB - SLOTP * thread_room st) end.
Definition prov_q (st : rtstate) : Z := NB * qc_bytes (st_qthread st) / 2^20.
Definition PTRC : Z := 2^17 + 2^14.
Definition prov_ptr (st : rtstate) : Z := Z.max 0 (PTRC - 16 * (st_nreserved st - nsec st)).
Definition fp (n : Z) : Z := 32 + n / 32.                        (* [comment removed for export] *)
Definition rp (n : Z) : Z := if bprim n then 0 else 2 * smapsize n.  (* [comment removed for export] *)
Definition prov_live (st : rtstate) : Z := zsum (map (fun b => fp (snd b) + rp (snd b)) (st_lb st)).
Definition prov_quar (st : rtstate) : Z := zsum (map (fun b => rp (snd b)) (qelems st ++ st_qpend st)).
Definition prov_depot (st : rtstate) : Z :=
  NODEBLOCK_SIZE * (DEPOT_NNB_MAX - d_nnb (st_depot st)) + STOREBLOCK_SIZE * (DEPOT_NSB_MAX - d_nsb (st_depot st)).
(* [comment removed for export] *)
Definition prov_slots (st : rtstate) : Z := SEC_SLOT_TAX * nsec st.
(* [comment removed for export] *)
Definition prov_l24 (st : rtstate) : Z := CL24_TAX * zlen (lb_prim st 24).
(* [comment removed for export] *)
Definition prov_emb (st : rtstate) : Z := if emb_d st =? 0 then EMB_CAP else 0.
Definition rt_prov (st : rtstate) : Z :=
  prov_classes st + prov_nb st + prov_q st + prov_ptr st + prov_live st + prov_quar st + prov_depot st + prov_slots st
  + prov_l24 st + prov_emb st.

(* [comment removed for export] *)
Lemma fp_nonneg : forall n, 0 <= n -> 0 <= fp n.
Proof. intros. unfold fp. apply Z.add_nonneg_nonneg; [lia|]. apply Z.div_pos; lia. Qed.
Lemma rp_nonneg : forall n, 0 <= rp n.
Proof.
  intros. unfold rp. destruct (bprim n); [lia|]. unfold smapsize, roundup.
  pose proof (Z.div_pos (needed n + 4096 - 1) 4096). unfold needed, needed0, rounded8, rz_size, roundup in *.
  assert (0 <= Z.shiftl 16 (rz_log n)) by (rewrite Z.shiftl_nonneg; lia).
  assert (0 <= (Z.max n 8 + 8 - 1) / 8 * 8) by (apply Z.mul_nonneg_nonneg; [apply Z.div_pos|]; lia).
  destruct (is_primary n); nia.
Qed.

Lemma zsum_nonneg : forall l, Forall (fun x => 0 <= x) l -> 0 <= zsum l.
Proof. induction l; intros H; cbn; [lia|]. inversion H; subst. unfold zsum in *. cbn. specialize (IHl H3). lia. Qed.

Lemma prov_live_nonneg : forall st, Forall (fun b => 0 <= snd b) (st_lb st) -> 0 <= prov_live st.
Proof.
  intros st H. unfold prov_live. apply zsum_nonneg. apply Forall_map. eapply Forall_impl; [|exact H].
  intros [A n] Hn. cbn [snd] in *. pose proof (fp_nonneg n Hn). pose proof (rp_nonneg n). lia.
Qed.
Lemma prov_quar_nonneg : forall st, 0 <= prov_quar st.
Proof. intros st. unfold prov_quar. apply zsum_nonneg. apply Forall_map. apply Forall_forall. intros [A n] _. apply rp_nonneg. Qed.
Lemma prov_classes_nonneg : forall st, 0 <= prov_classes st.
Proof. intros. unfold prov_classes. apply zsum_nonneg. apply Forall_map. apply Forall_forall. intros c _. unfold provU, provF. lia. Qed.
Lemma prov_q_nonneg : forall st, 0 <= qc_bytes (st_qthread st) -> 0 <= prov_q st.
Proof. intros. unfold prov_q, NB. apply Z.div_pos; lia. Qed.
Lemma prov_slots_nonneg : forall st, 0 <= prov_slots st.
Proof. intros. unfold prov_slots, SEC_SLOT_TAX, nsec. pose proof (zlen_nonneg (st_sec st)). lia. Qed.
Lemma prov_l24_nonneg : forall st, 0 <= prov_l24 st.
Proof. intros. unfold prov_l24, CL24_TAX. pose proof (zlen_nonneg (lb_prim st 24)). lia. Qed.
Lemma prov_emb_nonneg : forall st, 0 <= prov_emb st <= EMB_CAP.
Proof. intros. unfold prov_emb, EMB_CAP. destruct (emb_d st =? 0); lia. Qed.

(* [comment removed for export] *)
Lemma nexh_bound_wf : forall st, RTWF st -> 0 <= nexh st <= 32.
Proof. intros st WF. apply nexh_bound. exact (wb_len_regions st (wf_base_ok st WF)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma csize_pos : forall c, 1 <= c <= 31 -> 32 <= csize c.
Proof.
  intros c Hc. unfold csize. destruct (Z.eqb_spec c 31); [lia|]. destruct (Z.leb_spec c 16); [lia|].
  assert (H1 : 0 <= (c - 16) / 2) by (apply Z.div_pos; lia).
  assert (H2 : 512 <= Z.shiftl 512 ((c - 16) / 2)).
  { rewrite Z.shiftl_mul_pow2 by lia. pose proof (Z.pow_le_mono_r 2 0 ((c-16)/2) ltac:(lia) H1). change (2^0) with 1 in *. nia. }
  destruct (Z.odd (c - 16)); [|lia]. pose proof (Z.div_pos (Z.shiftl 512 ((c - 16) / 2)) 2 ltac:(lia) ltac:(lia)). lia.
Qed.

Lemma csize_mod32 : forall c, 1 <= c <= 31 -> csize c mod 32 = 0.
Proof.
  intros c Hc. unfold csize. destruct (Z.eqb_spec c 31); [reflexivity|]. destruct (Z.leb_spec c 16).
  - rewrite Z.mul_comm. apply Z_mod_mult.
  - assert (H1 : 0 <= (c - 16) / 2) by (apply Z.div_pos; lia).
    assert (Hd : 17 <= c <= 30) by lia.
    (* [comment removed for export] *)
    assert (E : exists k, c = k /\ (17 <= k <= 30)) by (exists c; lia). destruct E as (k & -> & Hk).
    destruct (Z.eq_dec k 17) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 18) as [->|]; [reflexivity|].
    destruct (Z.eq_dec k 19) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 20) as [->|]; [reflexivity|].
    destruct (Z.eq_dec k 21) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 22) as [->|]; [reflexivity|].
    destruct (Z.eq_dec k 23) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 24) as [->|]; [reflexivity|].
    destruct (Z.eq_dec k 25) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 26) as [->|]; [reflexivity|].
    destruct (Z.eq_dec k 27) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 28) as [->|]; [reflexivity|].
    destruct (Z.eq_dec k 29) as [->|]; [reflexivity|]. destruct (Z.eq_dec k 30) as [->|]; [reflexivity|]. lia.
Qed.


End CeilWrap.
