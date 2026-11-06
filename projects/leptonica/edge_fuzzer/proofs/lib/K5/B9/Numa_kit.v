(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface D_kit Lept_kit Lept_iface Lept_objkit LeptL_kit Ed_fp Ed_iface LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cells_bytes_mapC4 : forall ws, cells_bytes (map C4 ws) = u32s ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_bytes cbytes u32s]. rewrite IH. reflexivity. Qed.
Lemma cells_size_mapC4 : forall ws, cells_size (map C4 ws) = (4 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [map cells_size csize length]. rewrite IH. lia. Qed.
Lemma cells_wf_mapC4 : forall ws, cells_wf (map C4 ws).
Proof. induction ws as [|w ws IH]; [exact I|]. cbn. split; [exact I| exact IH]. Qed.

Lemma firstn_app_exact : forall {X} (a b : list X), firstn (length a) (a ++ b) = a.
Proof. intros X a b. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity. Qed.
Lemma skipn_app_exact : forall {X} (a b : list X), skipn (length a) (a ++ b) = b.
Proof. intros X a b. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.
Lemma upd_app_mid : forall {X} (a : list X) x b y, upd (a ++ x :: b) (length a) y = a ++ y :: b.
Proof. intros X a. induction a as [|z a IH]; intros x b y; [reflexivity|]. cbn. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma numa_arr_view : forall (m : mem) arr cap vals junk, rw_cells asegs m arr (numa_arr_cells cap vals junk) ->
  Z.of_nat (length vals) <= cap ->
  exists ws, u32arr asegs m arr (vals ++ ws) /\ Z.of_nat (length (vals ++ ws)) = cap.
Proof.
  intros m arr cap vals junk [[Hwf Hb] Hw] Hn. unfold numa_arr_cells in *.
  apply cells_wf_app in Hwf. destruct Hwf as [_ [Lj _]]. cbn [cell_wf] in Lj.
  rewrite cells_bytes_app, cells_bytes_mapC4 in Hb. cbn [cells_bytes cbytes] in Hb. rewrite app_nil_r in Hb.
  rewrite cells_size_app, cells_size_mapC4 in Hw. cbn [cells_size csize] in Hw. rewrite Nat.add_0_r in Hw.
  destruct (u32s_exists (Z.to_nat (cap - Z.of_nat (length vals))) junk ltac:(rewrite Lj; lia)) as (ws & E & Lw).
  exists ws. split.
  - split; [rewrite u32s_app, E; exact Hb|]. rewrite length_app.
    replace (4 * Z.of_nat (length vals + length ws)) with (Z.of_nat (4 * length vals + Z.to_nat (4 * cap - 4 * Z.of_nat (length vals)))) by lia. exact Hw.
  - rewrite length_app. lia.
Qed.

(* [comment removed for export] *)
Lemma numa_arr_unview : forall (m : mem) arr cap ws (n : nat), u32arr asegs m arr ws -> Z.of_nat (length ws) = cap -> (n <= length ws)%nat ->
  rw_cells asegs m arr (numa_arr_cells cap (firstn n ws) (u32s (skipn n ws))).
Proof.
  intros m arr cap ws n [Hb Hw] L Hn. unfold numa_arr_cells.
  assert (Lf : length (firstn n ws) = n) by (rewrite firstn_length_le; lia).
  split; [split|].
  - apply cells_wf_app. split; [apply cells_wf_mapC4|]. cbn [cells_wf cell_wf]. split; [| exact I].
    rewrite u32s_length, length_skipn, Lf. lia.
  - rewrite cells_bytes_app, cells_bytes_mapC4. cbn [cells_bytes cbytes]. rewrite app_nil_r, <- u32s_app, firstn_skipn. exact Hb.
  - rewrite cells_size_app, cells_size_mapC4. cbn [cells_size csize]. rewrite Nat.add_0_r, Lf.
    replace (Z.of_nat (4 * n + Z.to_nat (4 * cap - 4 * Z.of_nat n))) with (4 * Z.of_nat (length ws)) by lia. exact Hw.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma numa_obj_facts : forall live m na cap arr vals, numa_obj live m na cap arr vals ->
  Z.of_nat (length vals) <= cap /\ 1 <= cap <= 25600 /\ 0 < na /\ na mod 16 = 0 /\ 0 < arr /\ arr mod 16 = 0
  /\ In (na, 32) live /\ In (arr, 4 * cap) live /\ arr <> na.
Proof.
  intros live m na cap arr vals (_ & _ & (I1 & P1 & A1 & _) & (I2 & P2 & A2 & _) & D & C & N). repeat split; first [assumption | lia].
Qed.

Lemma chunk_mono : forall live live' p k, (forall e, In e live -> In e live') -> chunk live p k -> chunk live' p k.
Proof. intros live live' p k S (I & R). split; [exact (S _ I) | exact R]. Qed.

(* [comment removed for export] *)
Lemma lrm_cons : forall p e (l : list (Z * Z)), live_remove p (e :: l) = if fst e =? p then live_remove p l else e :: live_remove p l.
Proof. intros p e l. unfold live_remove. cbn. destruct (fst e =? p); cbn; reflexivity. Qed.

(* [comment removed for export] *)
Lemma numa_obj_mono : forall live live' m na cap arr vals, (forall e, In e live -> In e live') ->
  numa_obj live m na cap arr vals -> numa_obj live' m na cap arr vals.
Proof.
  intros live live' m na cap arr vals S (C & U & K1 & K2 & R).
  split; [exact C|]. split; [exact U|]. split; [exact (chunk_mono _ _ _ _ S K1)|]. split; [exact (chunk_mono _ _ _ _ S K2)| exact R].
Qed.

(* [comment removed for export] *)
Lemma numa_obj_keep : forall live (m m' : mem) na cap arr vals, keeps_live live m m' ->
  numa_obj live m na cap arr vals -> numa_obj live m' na cap arr vals.
Proof.
  intros live m m' na cap arr vals K ((pad & C) & (junk & U) & K1 & K2 & D & CP & N).
  split; [| split; [| exact (conj K1 (conj K2 (conj D (conj CP N))))]].
  - exists pad. destruct K1 as (Hin & _).
    apply (keeps_live_cells live m m' na 32 na _ K Hin); [lia| cbn; lia | exact C].
  - exists junk. destruct K2 as (Hin & _).
    apply (keeps_live_cells live m m' arr (4 * cap) arr _ K Hin); [lia| | exact U].
    unfold numa_arr_cells. rewrite cells_size_app, cells_size_mapC4. cbn [cells_size csize]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma numa_val_read : forall live m na cap arr vals i w, numa_obj live m na cap arr vals ->
  nth_error vals (Z.to_nat i) = Some w -> 0 <= i ->
  ov_read_bytes asegs m (wa (arr + 4 * i)) 4 = Some (le4 w).
Proof.
  intros live m na cap arr vals i w (_ & (junk & U) & _ & _ & _ & _ & N) Hw Hi.
  destruct (numa_arr_view m arr cap vals junk U N) as (ws & UA & L).
  apply (u32arr_read asegs m arr (vals ++ ws) i w _ UA); [| exact Hi| reflexivity].
  rewrite nth_error_app1; [exact Hw|]. exact (nth_error_lt _ _ _ Hw).
Qed.

(* [comment removed for export] *)
Lemma numa_ints_nth : forall vals ks i, numa_ints vals ks -> (Z.to_nat i < length vals)%nat ->
  exists k, nth_error ks (Z.to_nat i) = Some k /\ nth_error vals (Z.to_nat i) = Some (ival_w k) /\ loc_ok k.
Proof.
  intros vals ks i (E & F) Hi. subst vals. rewrite length_map in Hi.
  destruct (nth_error ks (Z.to_nat i)) as [k|] eqn:Hk; [| apply nth_error_None in Hk; lia].
  exists k. split; [reflexivity|]. split; [rewrite nth_error_map, Hk; reflexivity|].
  rewrite Forall_forall in F. apply F. eapply nth_error_In; exact Hk.
Qed.

Lemma numa_int_read : forall live m na cap arr vals ks i, numa_obj live m na cap arr vals -> numa_ints vals ks ->
  0 <= i < Z.of_nat (length vals) ->
  exists k, nth_error ks (Z.to_nat i) = Some k /\ loc_ok k /\ ov_read_bytes asegs m (wa (arr + 4 * i)) 4 = Some (le4 (ival_w k)).
Proof.
  intros live m na cap arr vals ks i OB IV Hi.
  destruct (numa_ints_nth vals ks i IV ltac:(lia)) as (k & Hk & Hw & R). exists k. split; [exact Hk|]. split; [exact R|].
  exact (numa_val_read live m na cap arr vals i _ OB Hw ltac:(lia)).
Qed.

(* [comment removed for export] *)
Lemma numa_app_store_ok : forall (m : mem) arr cap vals junk, rw_cells asegs m arr (numa_arr_cells cap vals junk) ->
  Z.of_nat (length vals) < cap -> store_ok asegs m (wa (arr + 4 * Z.of_nat (length vals))) 4 = true.
Proof.
  intros m arr cap vals junk U Hn. destruct (numa_arr_view m arr cap vals junk U ltac:(lia)) as (ws & UA & L).
  apply (u32arr_store_ok asegs m arr (vals ++ ws) (Z.of_nat (length vals)) _ UA); [rewrite length_app in L |- *; lia| reflexivity].
Qed.

Lemma numa_app_write : forall (m : mem) arr cap vals junk (v : word), rw_cells asegs m arr (numa_arr_cells cap vals junk) ->
  Z.of_nat (length vals) < cap ->
  exists junk', rw_cells asegs (write_to_mem m (wa (arr + 4 * Z.of_nat (length vals))) (le4 v)) arr (numa_arr_cells cap (vals ++ [v]) junk').
Proof.
  intros m arr cap vals junk v U Hn. destruct (numa_arr_view m arr cap vals junk U ltac:(lia)) as (ws & UA & L).
  rewrite length_app in L.
  destruct ws as [|w0 ws']; [cbn [length] in L; lia|].
  pose proof (u32arr_write asegs m arr (vals ++ w0 :: ws') (Z.of_nat (length vals)) v UA ltac:(rewrite length_app; cbn [length]; lia)) as UA'.
  rewrite Nat2Z.id, upd_app_mid in UA'.
  exists (u32s ws').
  pose proof (numa_arr_unview _ arr cap (vals ++ v :: ws') (length (vals ++ [v])) UA'
                ltac:(rewrite !length_app in *; cbn [length] in *; lia) ltac:(rewrite !length_app; cbn [length]; lia)) as R.
  replace (vals ++ v :: ws') with ((vals ++ [v]) ++ ws') in R by (rewrite <- app_assoc; reflexivity).
  rewrite firstn_app_exact, skipn_app_exact in R. exact R.
Qed.

(* [comment removed for export] *)
Lemma numa_ints_app : forall vals ks k, numa_ints vals ks -> loc_ok k -> numa_ints (vals ++ [ival_w k]) (ks ++ [k]).
Proof.
  intros vals ks k (E & F) Hk. split; [rewrite E, map_app; reflexivity|].
  apply Forall_app. split; [exact F| constructor; [exact Hk| constructor]].
Qed.
Lemma numa_ints_nil : numa_ints [] [].
Proof. split; [reflexivity| constructor]. Qed.
Lemma numa_ints_length : forall vals ks, numa_ints vals ks -> length vals = length ks.
Proof. intros vals ks (E & _). subst vals. apply length_map. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma numa_arr_fresh : forall (m : mem) arr cap bs, rw_cells asegs m arr [CB (Z.to_nat (4 * cap)) bs] -> 0 <= cap ->
  rw_cells asegs m arr (numa_arr_cells cap [] bs).
Proof.
  intros m arr cap bs U Hc. unfold numa_arr_cells. cbn [map app length Z.of_nat]. rewrite Z.mul_0_r, Z.sub_0_r. exact U.
Qed.

(* [comment removed for export] *)
