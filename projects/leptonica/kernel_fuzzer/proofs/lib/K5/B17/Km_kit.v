(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Wf_nat.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import ImageA.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.Lib Require Import RzCPS NodesA Arr.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import Layout.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.K5.B17 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit Lept_deserkit Km_setelem Km_iface.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cps_loop_Z : forall (I : Z -> config -> Prop) (X : config -> Prop) (N : Z),
  (forall i, 0 <= i < N -> cps asegs (I i) (fun c => (i + 1 < N /\ I (i + 1) c) \/ (i + 1 = N /\ X c))) ->
  forall i, 0 <= i < N -> cps asegs (I i) X.
Proof.
  intros I X N STEP.
  assert (G : forall k i, Z.to_nat (N - i) = k -> 0 <= i < N -> cps asegs (I i) X).
  { intros k. induction k as [k IH] using lt_wf_ind. intros i Hk Hi T c HI Hc.
    apply (STEP i Hi T c HI). intros c' [[Hlt HI']|[Heq HX]].
    - apply (IH (Z.to_nat (N - (i + 1)))) with (i + 1); [lia| reflexivity| lia| exact HI'| exact Hc].
    - apply Hc. exact HX. }
  intros i Hi. exact (G _ i eq_refl Hi).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma lrm_cons : forall p e l, live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof. intros p e l. unfold live_remove. cbn. destruct (fst e =? p); cbn; reflexivity. Qed.
Lemma live_remove_notin : forall p (l : list (Z * Z)), ~ In p (map fst l) -> live_remove p l = l.
Proof.
  intros p l. induction l as [|e l IH]; intros H; [reflexivity|]. rewrite lrm_cons.
  replace (fst e =? p) with false by (symmetry; apply Z.eqb_neq; intro E; apply H; left; exact E).
  f_equal. apply IH. intros Hx. apply H. right. exact Hx.
Qed.
Lemma lrm_app : forall p (l1 l2 : list (Z * Z)), live_remove p (l1 ++ l2) = live_remove p l1 ++ live_remove p l2.
Proof.
  intros p l1 l2. induction l1 as [|e l1 IH]; [reflexivity|]. cbn [app]. rewrite !lrm_cons.
  destruct (fst e =? p); [exact IH| cbn [app]; f_equal; exact IH].
Qed.
Lemma lrm_in_neq : forall p (l : list (Z * Z)) e, In e (live_remove p l) -> fst e <> p.
Proof.
  intros p l e. induction l as [|x l IH]; [cbn; intros []|]. rewrite lrm_cons.
  destruct (fst x =? p) eqn:E; [exact IH|]. intros [<-|H]; [apply Z.eqb_neq; exact E| exact (IH H)].
Qed.
Lemma live_remove_app_notin : forall p l1 l2, ~ In p (map fst l1) -> live_remove p (l1 ++ l2) = l1 ++ live_remove p l2.
Proof. intros p l1 l2 H. rewrite lrm_app, (live_remove_notin p l1 H). reflexivity. Qed.

Lemma rows_remove_nil : forall l, rows_remove [] l = l.
Proof. reflexivity. Qed.
Lemma rows_remove_cons : forall r rs l, rows_remove (r :: rs) l = rows_remove rs (live_remove r l).
Proof. reflexivity. Qed.
Lemma rows_remove_snoc : forall rs r l, rows_remove (rs ++ [r]) l = live_remove r (rows_remove rs l).
Proof. intros rs r l. unfold rows_remove. rewrite fold_left_app. reflexivity. Qed.

Lemma rows_remove_in : forall rs l e, In e l -> ~ In (fst e) rs -> In e (rows_remove rs l).
Proof.
  induction rs as [|r rs IH]; intros l e Hin Hn; [exact Hin|]. rewrite rows_remove_cons. apply IH.
  - apply live_remove_keep; [exact Hin|]. intros E. apply Hn. left. symmetry. exact E.
  - intros H. apply Hn. right. exact H.
Qed.
Lemma rows_remove_sub : forall rs l e, In e (rows_remove rs l) -> In e l.
Proof.
  induction rs as [|r rs IH]; intros l e H; [exact H|]. rewrite rows_remove_cons in H. apply IH in H. exact (live_remove_sub _ _ _ H).
Qed.

(* [comment removed for export] *)
Lemma rows_remove_app_all : forall rs X Y, (forall e, In e X -> In (fst e) rs) -> (forall e, In e Y -> ~ In (fst e) rs) ->
  rows_remove rs (X ++ Y) = Y.
Proof.
  induction rs as [|r rs IH]; intros X Y HX HY.
  - destruct X as [|e X]; [reflexivity|]. exfalso. exact (HX e (or_introl eq_refl)).
  - rewrite rows_remove_cons, lrm_app.
    rewrite (live_remove_notin r Y) by (intros Hin; apply in_map_iff in Hin as (e & E & He); apply (HY e He); rewrite E; left; reflexivity).
    apply IH.
    + intros e He. pose proof (lrm_in_neq _ _ _ He) as NE. apply live_remove_sub in He.
      destruct (HX e He) as [E|H]; [exfalso; apply NE; symmetry; exact E| exact H].
    + intros e He Hin. apply (HY e He). right. exact Hin.
Qed.

(* [comment removed for export] *)
Lemma rows_remove_app : forall a b l, rows_remove (a ++ b) l = rows_remove b (rows_remove a l).
Proof. intros a b l. unfold rows_remove. apply fold_left_app. Qed.
Lemma rows_remove_firstn_sub : forall n rs l e, In e (rows_remove rs l) -> In e (rows_remove (firstn n rs) l).
Proof.
  intros n rs l e H. rewrite <- (firstn_skipn n rs) in H. rewrite rows_remove_app in H. exact (rows_remove_sub _ _ _ H).
Qed.
Lemma firstn_S_nth : forall (rs : list Z) i, (i < length rs)%nat -> firstn (S i) rs = firstn i rs ++ [nth i rs 0].
Proof.
  induction rs as [|x rs IH]; intros i Hi; [cbn in Hi; lia|]. destruct i as [|i]; [reflexivity|].
  cbn [firstn nth app]. rewrite (IH i) by (cbn in Hi; lia). reflexivity.
Qed.
Lemma rows_remove_firstn_S : forall rs i l, (i < length rs)%nat ->
  rows_remove (firstn (S i) rs) l = live_remove (nth i rs 0) (rows_remove (firstn i rs) l).
Proof. intros rs i l Hi. rewrite (firstn_S_nth rs i Hi). apply rows_remove_snoc. Qed.
Lemma nodup_nth_notin_firstn : forall (rs : list Z) i, List.NoDup rs -> (i < length rs)%nat -> ~ In (nth i rs 0) (firstn i rs).
Proof.
  intros rs i ND Hi.
  destruct (nth_error_split rs i (nth i rs 0) (nth_error_nth' rs 0 Hi)) as (l1 & l2 & E & L1).
  assert (F : firstn i rs = l1).
  { rewrite E, firstn_app, L1, Nat.sub_diag, firstn_O, app_nil_r. apply firstn_all2. lia. }
  rewrite F. rewrite E in ND. apply List.NoDup_remove_2 in ND. intros Hin. apply ND. apply in_or_app. left. exact Hin.
Qed.

(* [comment removed for export] *)
Definition km_chunks (kel data sy sx : Z) (rows : list Z) : list (Z * Z) :=
  (kel, 24) :: (data, 8 * sy) :: map (fun r => (r, 4 * sx)) rows.

Lemma km_unlive_live : forall kel data sy sx rows live,
  List.NoDup (kel :: data :: rows) -> (forall x, In x (kel :: data :: rows) -> ~ In x (map fst live)) ->
  km_unlive kel data rows (km_live kel data sy sx rows live) = live.
Proof.
  intros kel data sy sx rows live ND HN. unfold km_unlive, km_live.
  apply List.NoDup_cons_iff in ND as (NK & ND). apply List.NoDup_cons_iff in ND as (ND0 & _).
  rewrite (rows_remove_app_all rows (rev (map (fun r => (r, 4 * sx)) rows))).
  - rewrite lrm_cons. cbn [fst]. rewrite Z.eqb_refl. rewrite lrm_cons. cbn [fst].
    replace (kel =? data) with false by (symmetry; apply Z.eqb_neq; intros E; apply NK; left; symmetry; exact E).
    rewrite (live_remove_notin data live) by (apply HN; right; left; reflexivity).
    rewrite lrm_cons. cbn [fst]. rewrite Z.eqb_refl. apply live_remove_notin. apply HN. left. reflexivity.
  - intros e He. apply in_rev in He. apply in_map_iff in He as (r & <- & Hr). exact Hr.
  - intros e [<-|[<-|He]]; cbn [fst].
    + intros Hr. apply ND0. exact Hr.
    + intros Hr. apply NK. right. exact Hr.
    + intros Hr. apply (HN (fst e)); [right; right; exact Hr| apply in_map; exact He].
Qed.

(* [comment removed for export] *)
Lemma rm_opt_app_notin : forall p l1 l2, (p <> 0 -> ~ In p (map fst l1)) -> rm_opt p (l1 ++ l2) = l1 ++ rm_opt p l2.
Proof.
  intros p l1 l2 H. unfold rm_opt. destruct (p =? 0) eqn:E; [reflexivity|]. apply Z.eqb_neq in E.
  apply live_remove_app_notin. exact (H E).
Qed.

Lemma km_live_in_kel : forall kel data sy sx rows live, In (kel, 24) (km_live kel data sy sx rows live).
Proof. intros. unfold km_live. apply in_or_app. right. right. left. reflexivity. Qed.
Lemma km_live_in_data : forall kel data sy sx rows live, In (data, 8 * sy) (km_live kel data sy sx rows live).
Proof. intros. unfold km_live. apply in_or_app. right. left. reflexivity. Qed.
Lemma km_live_in_row : forall kel data sy sx rows live r, In r rows -> In (r, 4 * sx) (km_live kel data sy sx rows live).
Proof. intros. unfold km_live. apply in_or_app. left. apply in_rev. rewrite rev_involutive. apply (in_map (fun r => (r, 4 * sx))). assumption. Qed.
Lemma km_live_in_old : forall kel data sy sx rows live e, In e live -> In e (km_live kel data sy sx rows live).
Proof. intros. unfold km_live. apply in_or_app. right. right. right. assumption. Qed.
Lemma km_live_inv : forall kel data sy sx rows live e,
  In e (km_live kel data sy sx rows live) -> In e (km_chunks kel data sy sx rows) \/ In e live.
Proof.
  intros kel data sy sx rows live e H. unfold km_live in H. apply in_app_or in H as [H|[<-|[<-|H]]].
  - left. right. right. apply in_rev in H. exact H.
  - left. right. left. reflexivity.
  - left. left. reflexivity.
  - right. exact H.
Qed.

(* [comment removed for export] *)
Lemma km_cost_bound : forall h w, 3 <= h -> 3 <= w -> w * h <= 2^26 -> km_cost h w + w * h + 2 <= 2^30.
Proof.
  intros h w Hh Hw Hwh. unfold km_cost, mcost.
  destruct (Z.leb_spec (8 * h) 64512) as [A|A]; destruct (Z.leb_spec (4 * w) 64512) as [B|B].
  - nia.
  - assert (h <= 4160) by nia. nia.
  - assert (h <= 22369622) by nia. nia.
  - assert (h <= 4160) by nia. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma u32arr_agree_nw : forall (m m' : mem) a ws, u32arr asegs m a ws ->
  agree_on (fun x => a <= x < a + 4 * Z.of_nat (length ws)) m m' -> u32arr asegs m' a ws.
Proof.
  intros m m' a ws [Hb Hw] HA. split.
  - apply (bytes_at_agree asegs m m' a _ Hb). rewrite u32s_length. eapply agree_sub; [exact HA|]. intros x Hx. cbv beta in *. lia.
  - apply (wr_at_agree_nw asegs m m' a _ Hw). eapply agree_sub; [exact HA|]. intros x Hx. cbv beta in *. lia.
Qed.

Lemma keeps_live_u64arr : forall live (m m' : mem) p n A ws, keeps_live live m m' -> In (p, n) live ->
  p <= A -> A + 8 * Z.of_nat (length ws) <= p + n -> u64arr asegs m A ws -> u64arr asegs m' A ws.
Proof.
  intros live m m' p n A ws K Hin H1 H2 H. apply (u64arr_agree_nw asegs m m' A ws H). intros a Ha. apply (K p n Hin a). lia.
Qed.
Lemma keeps_live_u32arr : forall live (m m' : mem) p n A ws, keeps_live live m m' -> In (p, n) live ->
  p <= A -> A + 4 * Z.of_nat (length ws) <= p + n -> u32arr asegs m A ws -> u32arr asegs m' A ws.
Proof.
  intros live m m' p n A ws K Hin H1 H2 H. apply (u32arr_agree_nw m m' A ws H). intros a Ha. apply (K p n Hin a). lia.
Qed.

(* [comment removed for export] *)
Lemma u64arr_cell : forall (m : mem) A ws (i : Z) w, u64arr asegs m A ws -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i ->
  rw_cells asegs m (A + 8 * i) [C8 w].
Proof.
  intros m A ws i w [Hb Hw] Hn Hi.
  pose proof (nth_error_lt _ _ _ Hn) as Hlt.
  destruct (u64s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  rewrite Eu in Hb. apply bytes_at_app in Hb as (_ & Hb). apply bytes_at_app in Hb as (Hb & _).
  rewrite Hlu in Hb. replace (A + Z.of_nat (8 * Z.to_nat i)) with (A + 8 * i) in Hb by lia.
  split; [split; [cbn; tauto| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]|].
  cbn [cells_size csize]. apply (wr_at_sub m A (8 * Z.of_nat (length ws))); [exact Hw| lia| lia| lia].
Qed.
Lemma u32arr_cell : forall (m : mem) A ws (i : Z) w, u32arr asegs m A ws -> nth_error ws (Z.to_nat i) = Some w -> 0 <= i ->
  rw_cells asegs m (A + 4 * i) [C4 w].
Proof.
  intros m A ws i w [Hb Hw] Hn Hi.
  pose proof (nth_error_lt _ _ _ Hn) as Hlt.
  destruct (u32s_split _ _ _ Hn) as (pre & post & E & Hlen & Eu & Hlu).
  rewrite Eu in Hb. apply bytes_at_app in Hb as (_ & Hb). apply bytes_at_app in Hb as (Hb & _).
  rewrite Hlu in Hb. replace (A + Z.of_nat (4 * Z.to_nat i)) with (A + 4 * i) in Hb by lia.
  split; [split; [cbn; tauto| cbn [cells_bytes cbytes]; rewrite app_nil_r; exact Hb]|].
  cbn [cells_size csize]. apply (wr_at_sub m A (4 * Z.of_nat (length ws))); [exact Hw| lia| lia| lia].
Qed.

(* [comment removed for export] *)
Lemma wr_at_cell4 : forall (m : mem) A n j, wr_at asegs m A n -> 0 <= j -> 4 * j + 4 <= n ->
  exists x : word, rw_cells asegs m (A + 4 * j) [C4 x].
Proof.
  intros m A n j H Hj Hn.
  pose proof (wr_at_sub m A n (A + 4 * j) 4 H ltac:(lia) ltac:(lia) ltac:(lia)) as W.
  destruct (wr_at_rw_CB m (A + 4 * j) 4 W ltac:(lia)) as (junk & C). exact (cb4_c4' m (A + 4 * j) junk C).
Qed.
(* [comment removed for export] *)
Lemma wr_at_patch : forall (m m' : mem) A n c k, wr_at asegs m A n ->
  (forall a : word, A <= bv_unsigned a < A + n -> ~ (c <= bv_unsigned a < c + k) -> m' a = m a) ->
  wr_at asegs m' c k -> A <= c -> c + k <= A + n -> wr_at asegs m' A n.
Proof.
  intros m m' A n c k (H0 & H1 & H) HA (C0 & C1 & HC) Hc Hck. split; [exact H0|]. split; [exact H1|].
  intros i Hi. destruct (Z_lt_le_dec (A + i) c) as [L|L]; [| destruct (Z_lt_le_dec (A + i) (c + k)) as [L2|L2]].
  - rewrite (wview_agree asegs m m'); [exact (H i Hi)|]. apply HA; rewrite wa_unsigned_range by lia; lia.
  - replace (A + i) with (c + (A + i - c)) by lia. apply HC. lia.
  - rewrite (wview_agree asegs m m'); [exact (H i Hi)|]. apply HA; rewrite wa_unsigned_range by lia; lia.
Qed.

Lemma kel_obj_keep : forall live (m m' : mem) kel sy sx cy cx data rows, keeps_live live m m' ->
  kel_obj live m kel sy sx cy cx data rows -> kel_obj live m' kel sy sx cy cx data rows.
Proof.
  intros live m m' kel sy sx cy cx data rows K (KC & KCH & DA & DCH & LEN & ROWS & ND & SYB & SXB).
  split; [| split; [exact KCH|]].
  { destruct KCH as (Hin & _). apply (keeps_live_cells live m m' kel 24 kel _ K Hin); [lia| | exact KC]. cbn. lia. }
  split.
  { destruct DCH as (Hin & _). apply (keeps_live_u64arr live m m' data (8 * sy) data _ K Hin); [lia| | exact DA].
    rewrite length_map. lia. }
  split; [exact DCH| split; [exact LEN|]]. split; [| exact (conj ND (conj SYB SXB))].
  eapply Forall_impl; [| exact ROWS]. intros r (RCH & RW). split; [exact RCH|].
  destruct RCH as (Hin & _). apply (wr_at_agree_nw asegs m m' r (4 * sx) RW). intros a Ha. apply (K r (4 * sx) Hin a). lia.
Qed.

(* [comment removed for export] *)
Lemma kel_obj_move : forall live live' (m : mem) kel sy sx cy cx data rows,
  (forall e, In e (km_chunks kel data sy sx rows) -> In e live') ->
  kel_obj live m kel sy sx cy cx data rows -> kel_obj live' m kel sy sx cy cx data rows.
Proof.
  intros live live' m kel sy sx cy cx data rows HS (KC & (KI & K0 & K16 & KN) & DA & (DI & D0 & D16 & DN) & LEN & ROWS & ND & SYB & SXB).
  split; [exact KC|]. split; [split; [apply HS; left; reflexivity| repeat split; assumption]|].
  split; [exact DA|]. split; [split; [apply HS; right; left; reflexivity| repeat split; assumption]|].
  split; [exact LEN|]. split; [| exact (conj ND (conj SYB SXB))].
  apply Forall_forall. intros r Hr. rewrite Forall_forall in ROWS. destruct (ROWS r Hr) as ((RI & R0 & R16 & RN) & RW).
  split; [split; [apply HS; right; right; apply in_map_iff; exists r; split; [reflexivity| exact Hr]| repeat split; assumption]| exact RW].
Qed.

(* [comment removed for export] *)
Lemma kel_cells_of_zero : forall (m : mem) kel h w data junk, junk = repeat (Z_to_bv 8 0) 8 ->
  rw_cells asegs m kel [C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 w); CB 8 junk; C8 (Z_to_bv 64 data)] ->
  rw_cells asegs m kel (kel_cells h w 0 0 data).
Proof.
  intros m kel h w data junk -> [[Hwf Hb] Hw]. unfold kel_cells. split; [split|].
  - cbn. tauto.
  - replace (cells_bytes [C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 w); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 data)])
      with (cells_bytes [C4 (Z_to_bv 64 h); C4 (Z_to_bv 64 w); CB 8 (repeat (Z_to_bv 8 0) 8); C8 (Z_to_bv 64 data)]); [exact Hb|].
    cbn [cells_bytes cbytes]. reflexivity.
  - cbn in Hw |- *. exact Hw.
Qed.

(* [comment removed for export] *)
Lemma u64arr_nil : forall (m : mem) A, 0 <= A <= 2^64 -> u64arr asegs m A [].
Proof. intros m A H. split; [apply bytes_at_nil; lia| split; [lia| split; [cbn; lia| intros i Hi; cbn in Hi; lia]]]. Qed.
Lemma u64arr_snoc_write : forall (m : mem) A ws v, u64arr asegs m A ws -> wr_at asegs m (A + 8 * Z.of_nat (length ws)) 8 ->
  u64arr asegs (write_to_mem m (wa (A + 8 * Z.of_nat (length ws))) (le8 v)) A (ws ++ [v]).
Proof.
  intros m A ws v [Hb Hw] HW.
  pose proof (bytes_at_bound _ _ _ _ Hb) as (HB0 & HB1). pose proof HW as (W0 & W1 & _).
  rewrite u64s_length in HB1.
  split.
  - rewrite u64s_app. cbn [u64s]. rewrite app_nil_r. apply bytes_at_app. split.
    + apply (bytes_at_write_other asegs m (A + 8 * Z.of_nat (length ws)) (le8 v) A (u64s ws) Hb);
        [lia | rewrite length_le8; lia | left; rewrite u64s_length; lia].
    + rewrite u64s_length. replace (A + Z.of_nat (8 * length ws)) with (A + 8 * Z.of_nat (length ws)) by lia.
      apply bytes_at_write_same; [lia| rewrite length_le8; lia].
  - rewrite length_app. cbn [length]. replace (8 * Z.of_nat (length ws + 1)) with (8 * Z.of_nat (length ws) + 8) by lia.
    apply wr_at_app; [lia| lia|]. split; apply wr_at_write; assumption.
Qed.

Lemma sec_bytes_rev : forall l, sec_bytes (rev l) = sec_bytes l.
Proof.
  induction l as [|[p n] l IH]; [reflexivity|]. cbn [rev]. rewrite sec_bytes_app, IH. cbn [sec_bytes]. lia.
Qed.
Lemma sec_bytes_rows_le : forall (rs : list Z) n, 0 <= n -> sec_bytes (map (fun r => (r, n)) rs) <= Z.of_nat (length rs) * n.
Proof.
  intros rs n Hn. induction rs as [|r rs IH]; [cbn; lia|]. cbn [map length].
  pose proof (sec_bytes_cons_le r n (map (fun r => (r, n)) rs) Hn). lia.
Qed.
Lemma km_live_sec : forall kel data sy sx rows L, 0 <= sx -> 0 <= sy ->
  sec_bytes (km_live kel data sy sx rows L) <= Z.of_nat (length rows) * (4 * sx) + 8 * sy + sec_bytes L.
Proof.
  intros kel data sy sx rows L Hx Hy. unfold km_live. rewrite sec_bytes_app, sec_bytes_rev.
  pose proof (sec_bytes_rows_le rows (4 * sx) ltac:(lia)).
  pose proof (sec_bytes_cons_le data (8 * sy) ((kel, 24) :: L) ltac:(lia)).
  rewrite (sec_bytes_cons_small kel 24 L) in * by lia. lia.
Qed.
Lemma km_live_length : forall kel data sy sx rows L,
  Z.of_nat (length (km_live kel data sy sx rows L)) = Z.of_nat (length rows) + 2 + Z.of_nat (length L).
Proof. intros. unfold km_live. rewrite length_app, length_rev, length_map. cbn [length]. lia. Qed.
Lemma km_live_snoc : forall kel data sy sx rows r L,
  km_live kel data sy sx (rows ++ [r]) L = (r, 4 * sx) :: km_live kel data sy sx rows L.
Proof. intros. unfold km_live. rewrite map_app, rev_app_distr. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma nodup_of_apart : forall l : list (Z * Z),
  (forall l1 p n l2 q k, l = l1 ++ (p, n) :: l2 -> In (q, k) (l1 ++ l2) -> p + n <= q \/ q + k <= p) ->
  (forall p n, In (p, n) l -> 0 < n) -> List.NoDup (map fst l).
Proof.
  induction l as [|[p n] l IH]; intros D P; cbn [map fst]; [constructor|]. constructor.
  - intro Hin. apply in_map_iff in Hin. destruct Hin as ([q k] & E & Hq). cbn [fst] in E. subst q.
    pose proof (D [] p n l p k eq_refl Hq) as A. pose proof (P p n ltac:(left; reflexivity)). pose proof (P p k ltac:(right; exact Hq)). lia.
  - apply IH; [| intros q k Hq; apply (P q k); right; exact Hq].
    intros l1 q k l2 r j E Hr. apply (D ((p, n) :: l1) q k l2 r j); [rewrite E; reflexivity| right; exact Hr].
Qed.
Lemma nodup_app_notin : forall (l1 l2 : list Z) x, List.NoDup (l1 ++ l2) -> In x l2 -> ~ In x l1.
Proof.
  induction l1 as [|y l1 IH]; intros l2 x ND Hx; [intros []|]. cbn [app] in ND. apply List.NoDup_cons_iff in ND. destruct ND as [NI ND].
  intros [E|Hin]; [subst y; apply NI; apply in_or_app; right; exact Hx| exact (IH l2 x ND Hx Hin)].
Qed.

Lemma km_live_fst : forall kel data sy sx rows L,
  map fst (km_live kel data sy sx rows L) = rev rows ++ data :: kel :: map fst L.
Proof.
  intros. unfold km_live. rewrite map_app, map_rev, map_map. cbn [map fst]. rewrite map_id. reflexivity.
Qed.

Lemma km_live_nodup_split : forall kel data sy sx rows L,
  List.NoDup (map fst (km_live kel data sy sx rows L)) ->
  List.NoDup (kel :: data :: rows) /\ (forall x, In x (kel :: data :: rows) -> ~ In x (map fst L)).
Proof.
  intros kel data sy sx rows L ND. rewrite km_live_fst in ND.
  pose proof (List.NoDup_app_remove_l _ _ ND) as N1.
  apply List.NoDup_cons_iff in N1 as (D1 & N1). apply List.NoDup_cons_iff in N1 as (K1 & _).
  pose proof (List.NoDup_app_remove_r _ _ ND) as NR. apply NoDup_rev in NR. rewrite rev_involutive in NR.
  assert (RX : forall x, In x rows -> ~ In x (data :: kel :: map fst L)).
  { intros x Hx Hin. apply (nodup_app_notin _ _ x ND Hin). apply in_rev. rewrite rev_involutive. exact Hx. }
  split.
  - constructor; [| constructor; [| exact NR]].
    + intros [E|Hin]; [apply D1; left; symmetry; exact E| apply (RX kel Hin); right; left; reflexivity].
    + intros Hin. apply (RX data Hin). left. reflexivity.
  - intros x [<-|[<-|Hx]]; [exact K1| intros H; apply D1; right; exact H| intros H; apply (RX x Hx); right; right; exact H].
Qed.

Section KmArt.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma live_nodup : forall Σ m, ART RT Σ m -> (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) -> List.NoDup (map fst (rt_live RT Σ)).
Proof using AF.
  intros Σ m HA P. apply nodup_of_apart; [| exact P]. intros l1 p n l2 q k E Hq. exact (af_live_disj RT AF Σ m p n q k l1 l2 HA E Hq).
Qed.

(* [comment removed for export] *)
Lemma fresh_chunk_apart : forall Σ' (m : mem) l1 p n live0 frs usp a,
  ART RT Σ' m -> rt_live RT Σ' = l1 ++ (p, n) :: live0 -> rt_frames RT Σ' = frs ->
  rt_sp0 RT Σ' - STACK_WIN <= usp ->
  aclient live0 frs usp a -> a < p \/ p + n <= a.
Proof using AF.
  intros Σ' m l1 p n live0 frs usp a HA LV FRS SPL Ha.
  assert (INL : In (p, n) (rt_live RT Σ')) by (rewrite LV; apply in_or_app; right; left; reflexivity).
  pose proof (af_live_range RT AF Σ' m p n HA INL) as (P0 & PHI & PSEG).
  unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *.
  destruct Ha as [H|[H|[H|[H|H]]]].
  - right. lia.
  - pose proof (client_static_below a H) as HB. unfold SEGTOP_A in HB.
    destruct H as ((l & h & Hin & Hx) & _). unfold CLIENT_STATIC in Hin. cbn [In] in Hin.
    assert (X : 0x10000 <= a) by (repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]); destruct Hin).
    lia.
  - destruct H as (p' & n' & Hin & Hp).
    assert (Hin' : In (p', n') (l1 ++ live0)) by (apply in_or_app; right; exact Hin).
    pose proof (af_live_disj RT AF Σ' m p n p' n' l1 live0 HA LV Hin') as D. lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_frames_range RT AF Σ' m f k HA Hin) as (_ & _ & _ & FLV). specialize (FLV p n INL). lia.
  - destruct H as (f & k & Hin & Hf). rewrite <- FRS in Hin.
    pose proof (af_fshadow_apart RT AF Σ' m f k HA Hin) as (SA1 & _). specialize (SA1 p n INL). lia.
Qed.

(* [comment removed for export] *)
Lemma live_apart2 : forall Σ (m : mem) p n q k, ART RT Σ m -> In (p, n) (rt_live RT Σ) -> In (q, k) (rt_live RT Σ) -> p <> q ->
  p + n <= q \/ q + k <= p.
Proof using AF.
  intros Σ m p n q k HA H1 H2 NE. destruct (in_split _ _ H1) as (l1 & l2 & E).
  apply (af_live_disj RT AF Σ m p n q k l1 l2 HA E). rewrite E in H2. apply in_app_or in H2.
  apply in_or_app. destruct H2 as [H2|[H2|H2]]; [left; exact H2| injection H2 as -> ->; contradiction| right; exact H2].
Qed.
End KmArt.
