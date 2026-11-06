(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import AImages AImageFacts.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import STree.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanConsts AsanSizeClass AsanState AsanLayout AsanOps AsanHoare AsanPS AsanRep AsanKern AsanClient AsanWf1 AsanWf3 AsanBudget AsanDepot AsanRepFrame AsanRepFrame2 AsanRepEnqB AsanRepXferB AsanRepLdlB.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BF_free_kit BF_qkit B_benv5 BF_qrepL.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[warnings="-notation-for-abbreviation"] Notation mem := (word -> option byte).
#[warnings="-notation-for-abbreviation"] Notation wz := (fun z : Z => Z_to_bv 64 z).

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma blen_qcount : forall l, blen l = qcount l. Proof. intros l. reflexivity. Qed.
Lemma bhd_first : forall l, bhd l = list_first l. Proof. intros [|b l]; reflexivity. Qed.
Lemma blast_snoc : forall l b, blast (l ++ [b]) = b_addr b.
Proof.
  intros l b. induction l as [|b0 l IH]; [reflexivity|]. destruct l as [|b1 l']; [reflexivity|].
  cbn [app] in IH |- *. change (blast (b0 :: b1 :: l' ++ [b])) with (blast (b1 :: l' ++ [b])). exact IH.
Qed.
Lemma blast_last : forall l, blast l = list_last l.
Proof.
  intros l. induction l as [|b0 l0 _] using rev_ind; [reflexivity|].
  rewrite blast_snoc. unfold list_last. rewrite last_last. destruct (l0 ++ [b0]) eqn:E; [| reflexivity].
  exfalso. destruct l0; discriminate.
Qed.
(* [comment removed for export] *)
Lemma batch_list_of_views : forall (sx : astate) l (m : mem), bcells m l -> bitemsl m l -> arep_batch_list bsegs sx l m.
Proof.
  intros sx l m. induction l as [|b l IH]; intros BC BI; [exact I|].
  destruct BC as [HB BC']. destruct BI as [HI BI']. split; [| exact (IH BC' BI')].
  split; [destruct l; exact HB| exact HI].
Qed.

(* [comment removed for export] *)
Section QRep.
Variable E0 : aenv.
#[local] Notation T := (ae_thread E0).

(* [comment removed for export] *)
Definition xfer_st (a : astate) : astate := upd_tq (fun _ => []) (upd_gq (fun g => g ++ as_tq a) a).
Definition rmerge (gq : list batch) : list batch * list batch :=
  if (kBatchSize * zlen gq <? qbytes gq) && (qbytes gq * 100 <? kBatchSize * zlen gq * 200) then merge_batches gq else (gq, []).
Definition FPW4 (gq5 : list batch) (lo : Z) (z : Z) : Prop :=
     lo <= z
  \/ (ae_instance E0 + kInsQMutex <= z < ae_instance E0 + kInsQMutex + 4)
  \/ (ae_instance E0 + kInsQGlobal <= z < ae_instance E0 + kInsQGlobal + 32)
  \/ (T + kThrQCache <= z < T + kThrQCache + 32)
  \/ (exists b, In b gq5 /\ b_addr b <= z < b_addr b + 8192).

(* [comment removed for export] *)
Hypothesis IC0 : ae_ic E0 = both_ic.
Lemma img_inst_apart : forall r, In r (List.tl (arep_img_ranges E0) ++ depot_static E0) -> fst r + snd r <= ae_instance E0 \/ ae_instance E0 + 3632 <= fst r.
Proof.
  intros r Hr. unfold ae_instance. unfold arep_img_ranges, depot_static in Hr. rewrite IC0 in Hr |- *.
  cbn -[Z.add Z.mul Z.le] in Hr. repeat (destruct Hr as [<-|Hr]; [cbn; clear; lia|]). destruct Hr.
Qed.

(* [comment removed for export] *)
Theorem R4_holds :
  forall (a4 : astate) (m6 m8 : mem) (lo : Z) (gq1 emp popped kept : list batch),
  let gq5 := as_gq a4 ++ as_tq a4 in
  let a6 := upd_gq (fun _ => kept) (xfer_st a4) in
  as_tq a4 <> [] -> ARep bsegs E0 (DepotR bsegs E0) a4 m6 -> AWf E0 [] [] a4 -> renv_ok E0 a4 ->
  wmono bsegs m6 m8 -> (forall z, 0 <= z < 2^64 -> ~ FPW4 gq5 lo z -> m8 (wa z) = m6 (wa z)) -> alloc_ceiling <= lo ->
  rmerge gq5 = (gq1, emp) -> pop_prefix gq1 (qbytes gq1) kQuarantineMin = (popped, kept) ->
  rw_cells bsegs m8 (ae_instance E0 + kInsQMutex) [C4 (wz 0)] ->
  rw_cells bsegs m8 (ae_instance E0 + kInsQGlobal) [C8 (wz (blen kept)); C8 (wz (bhd kept)); C8 (wz (blast kept)); C8 (wz (qbytes kept))] ->
  rw_cells bsegs m8 (T + kThrQCache) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  bcells m8 kept -> bitemsl m8 kept ->
  ARep bsegs E0 (DepotR bsegs E0) a6 m8.
Proof.
  intros a4 m6 m8 lo gq1 emp popped kept gq5 a6 _ REP WF RENV WM AG LOC _ _ NCm NCg NCc BC BI.
  replace a6 with (qx_st a4 [] kept) by (subst a6; unfold qx_st, xfer_st; destruct a4; reflexivity).
  apply (ARep_q_xfer bsegs E0 [] a4 WF RENV img_inst_apart m6 m8 lo [] kept REP WM); [| exact LOC| exact NCm| | | exact I|].
  - intros z Hz NF. apply AG; [exact Hz|]. intros X. apply NF. unfold FPWq. unfold FPW4 in X.
    destruct X as [X|[X|[X|[X|(b & Hb & X)]]]]; [left; exact X| right; left; exact X| do 2 right; left; exact X| do 3 right; left; exact X|].
    do 4 right. exists b. split; [| exact X]. subst gq5. apply in_app_iff. apply in_app_iff in Hb. tauto.
  - rewrite blen_qcount, bhd_first, blast_last in NCg. exact NCg.
  - exact NCc.
  - exact (batch_list_of_views _ kept m8 BC BI).
Qed.

(* [comment removed for export] *)
Definition FPWx (a : astate) (lo : Z) (z : Z) : Prop :=
     lo <= z \/ (ae_instance E0 + kInsQMutex <= z < ae_instance E0 + kInsQMutex + 4)
  \/ (ae_instance E0 + kInsQGlobal <= z < ae_instance E0 + kInsQGlobal + 32)
  \/ (T + kThrQCache <= z < T + kThrQCache + 32)
  \/ (as_gq a <> [] /\ list_last (as_gq a) <= z < list_last (as_gq a) + 8).
Theorem R3_holds :
  forall (a : astate) (m m' : mem) (lo : Z),
  let tq := as_tq a in let gq := as_gq a in
  tq <> [] -> ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] [] a -> renv_ok E0 a ->
  wmono bsegs m m' -> (forall z, 0 <= z < 2^64 -> ~ FPWx a lo z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells bsegs m' (ae_instance E0 + kInsQMutex) [C4 (wz 0)] ->
  rw_cells bsegs m' (ae_instance E0 + kInsQGlobal)
    [C8 (wz (qcount gq + qcount tq)); C8 (wz (match gq with [] => list_first tq | _ => list_first gq end)); C8 (wz (list_last tq)); C8 (wz (gq_bytes a + tq_bytes a))] ->
  rw_cells bsegs m' (T + kThrQCache) [C8 (wz 0); C8 (wz 0); C8 (wz 0); C8 (wz 0)] ->
  (forall l0 b0, gq = l0 ++ [b0] -> rw_cells bsegs m' (b_addr b0) [C8 (wz (list_first tq))]) ->
  ARep bsegs E0 (DepotR bsegs E0) (xfer_st a) m'.
Proof.
  intros a m m' lo tq gq TQ REP WF RENV WM AG LOC NCm NCg NCc NCl.
  change (xfer_st a) with (qx_st a [] (gq ++ tq)).
  exact (ARep_after_xfer bsegs E0 [] a WF RENV img_inst_apart m m' lo TQ REP WM AG LOC NCm NCg NCc NCl).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma QPADR_holds : forall (a : astate) (m : mem), ARep bsegs E0 (DepotR bsegs E0) a m -> rw_cells bsegs m 0xab2ca [C2 (Z_to_bv 64 0)].
Proof.
  intros a m REP. pose proof REP as ((_ & _ & _ & _ & _ & _ & _ & _ & A9 & _) & _).
  unfold ae_instance in A9. rewrite IC0 in A9. cbn [aic_instance both_ic] in A9. unfold kInsQMutex in A9.
  match type of A9 with rw_cells _ _ ?x _ => replace x with 0xab2c8 in A9 by reflexivity end.
  assert (X : rw_cells bsegs m 0xab2c8 [C2 (Z_to_bv 64 0); C2 (Z_to_bv 64 0)]).
  { eapply BF_free_kit.rw_cells_reshape; [| | exact A9]; [cbn; auto| vm_compute; reflexivity]. }
  apply (BF_free_kit.rwc_split bsegs m _ [_] [_]) in X. destruct X as [_ X]. exact X.
Qed.

(* [comment removed for export] *)
Theorem R7_holds :
  forall (a : astate) (m m' : mem) (lo cb i0 j0 : Z) (i : nat) (D : list batch) (cm : chunkmeta) (sc : secchunk) (junk : list word),
  let n := cm_n cm in let A := sc_map_beg sc in let L := sc_map_size sc in let lastc := List.last (as_sec a) sc in
  let a' := BF_qrepL.ldl_st cb cm sc i a in let st := as_sec_stats a in let ts := as_ts a in
  as_chunks a !! cb = Some cm -> cm_state cm = CQuarantined i0 j0 -> cm_prim cm = None ->
  nth_error (as_sec a) i = Some sc -> cm_alloc_beg cm = A + kPageSize ->
  ARep bsegs E0 (DepotR bsegs E0) a m -> AWf E0 [] D a -> AsanRepEnqB.renv_ok E0 a ->
  (forall z, 0 <= z < 2^64 -> ~ BF_qrepL.FPW7 E0 a lo sc i z -> m' (wa z) = m (wa z)) -> alloc_ceiling <= lo ->
  rw_cells bsegs m' (ae_instance E0 + kInsNReserved) [C8 (wz (as_ptr_committed a)); C8 (wz (n_chunks a - 1)); C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs m' (ae_instance E0 + kInsSecStats) [C8 (wz (ss_n_allocs st)); C8 (wz (ss_n_frees st + 1)); C8 (wz (ss_cur st - L)); C8 (wz (ss_max st))] ->
  rw_cells bsegs m' (ae_instance E0 + kInsSecMutex) [C4 (wz 0)] ->
  rw_cells bsegs m' (ae_instance E0 + kInsGlobalStats + 16) [C8 (wz (as_glob_allocated a - L)); C8 (wz (as_glob_mapped a - L))] ->
  u64arr bsegs m' (ae_ptr_array E0) (map (fun c => wz (sc_map_beg c)) (as_sec a') ++ junk) -> (length (as_sec a') + length junk = Z.to_nat kChunksBlockCount)%nat ->
  (sc_map_beg lastc <> A -> rw_cells bsegs m' (sc_map_beg lastc + 24) [C8 (wz (Z.of_nat i))]) ->
  rw_cells bsegs m' (T + kThrStats + 40) [C8 (wz (ts_real_frees ts + 1)); C8 (wz (ts_really_freed ts + n))] ->
  rw_cells bsegs m' (T + kThrStats + 88) [C8 (wz (ts_munmaps ts + 1)); C8 (wz (ts_munmaped ts + L))] ->
  rw_cells bsegs m' (kShadowBase + A / 8) [CB (Z.to_nat (L / 8)) (repeat (Z_to_bv 8 0) (Z.to_nat (L / 8)))] ->
  ARep bsegs E0 (DepotR bsegs E0) a' m'.
Proof. exact (BF_qrepL.R7_holds E0 (fun r Hr => img_inst_apart r ltac:(apply in_app_iff; left; exact Hr))). Qed.
End QRep.
End RC__1.
