(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ACnt24.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModel.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AModelX.
Import ListNotations.
Open Scope Z_scope.

From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Ltac2 gd_tbl_APop () : Init.string Init.list := ["RocqVerifyHarness.AgentSubmission.BHeap.AModel.AH"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_reg"; "ARUN_1.Pop.pop_cache"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_cinit"; "Corelib.Init.Datatypes.cons"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.chunk"; "ARUN_1.Pop.newk"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_chunks"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_tq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_gq"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_sec"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.DP"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_ia"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_fake"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_pa_committed"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_havol"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_acct"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.ahst"; "Corelib.Numbers.BinNums.Z"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.hfr"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.FR_MAXm"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.s_total"; "RocqVerifyHarness.AgentSubmission.BHeap.AModel.h_dep"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.BHeap.AModelX.sframes"; "Stdlib.ZArith.BinInt.Z.pow"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.
#[using="Type"] Lemma last_nth : forall (l : list Z) d, l <> [] -> last l d = nth (length l - 1) l d.
Proof.
  intros l d NE. induction l as [|a l IH]; [congruence|]. destruct l as [|b l]; [reflexivity|].
  change (last (a :: b :: l) d) with (last (b :: l) d). rewrite (IH ltac:(discriminate)).
  change (length (a :: b :: l)) with (S (S (length l))). change (length (b :: l)) with (S (length l)).
  replace (S (S (length l)) - 1)%nat with (S (length l)) by lia. replace (S (length l) - 1)%nat with (length l) by lia. reflexivity.
Qed.

#[using="Type"] Lemma rz_size_bound' : forall n, 16 <= rz_size n <= 2048.
Proof. intros n. destruct (rz_size_cases n) as [E|[E|[E|[E|[E|[E|[E|E]]]]]]]; rewrite E; lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma hdr_in_slot : forall h k, wf_chunk' h k ->
  (if ck_prim k then ck_ab k else ck_map_beg k) <= ck_hdr k /\ ck_hdr k + 16 <= ck_end k.
Proof.
  (intros h k dd_H; ddestruct dd_H as (WN & _ & WP & WX)). unfold ck_hdr, ck_user, ck_rz, ck_end, ck_map_beg, ck_map_size, kChunkHeaderSize.
  pose proof (rz_size_bound' (ck_n k)) as RZ.
  destruct (ck_prim k) eqn:PR.
  - ddestruct WX as (WCLS & WC30 & _). rewrite WCLS.
    pose proof (needed_le_class (ck_n k) ltac:(lia) ltac:(rewrite <- WP; reflexivity)) as NC.
    unfold needed in NC. pose proof (rounded_spec (ck_n k) ltac:(lia)) as [R _]. lia.
  - unfold sec_map_size. pose proof (round_up_spec (needed2 (ck_n k)) 4096 ltac:(lia)) as [RU _].
    unfold needed2, needed in RU |- *. pose proof (rounded_spec (ck_n k) ltac:(lia)) as [R _].
    destruct (from_primary (ck_n k)); lia.
Qed.

Section Pop.
  Variable h : ahst.
  Variables (c q k n AB N' tf' : Z) (nb' bl' : list Z).
  Let L := h_L h.
  Let p := h_cache h c.

  Definition pop_cache (j : Z) : pcl := if j =? c then PC (pc_max p) (pc_csize p) (removelast (pc_chunks p)) else h_cache h j.
  Definition newk : chunk := CK AB n true c CHUNK_ALLOCATED.
  Definition pop_h : ahst := ltac2:(CDefT.buildp (gd_tbl_APop ()) "(0.VL,(1.Vh,)$2.(3.Vh,)(4.$5.$6.(7.Vh,))(8.Vh,)(9.Vh,)(:.Vh,)(;.VN',Vnb',Vtf',Vbl',)(<.Vh,)(=.Vh,)(>.Vh,)(?.Vh,)(10.Vh,))")
(* [comment removed for export] *).

  Hypothesis AWF : awf' h.
  Hypothesis GC : 1 <= c <= 30.
  Hypothesis NE : pc_chunks p <> [].
  (* [comment removed for export] *)
  Hypothesis XC24 : win24 n = true -> cnt24 (blocks h) < C24MAX.
  Hypothesis HQ : q = nth (length (pc_chunks p) - 1) (pc_chunks p) 0.
  Hypothesis HK : 0 <= k < carved h c /\ 16 * q = k * class_size c.
  Hypothesis EAB : AB = chunk_at L c k.
  Hypothesis NB : 0 <= n < 2^28.
  Hypothesis FP : from_primary n = true.
  Hypothesis EC : pclass n = c.
  Hypothesis OLDAP : Forall (fun k' => ck_end k' <= AB \/ AB + class_size c <= (if ck_prim k' then ck_ab k' else ck_map_beg k')) (h_chunks h).
  (* [comment removed for export] *)
  Hypothesis DN : d_n (h_dep h) <= N' <= d_n (h_dep h) + 1.
  Hypothesis DTF : s_total (h_dep h) <= tf'.
  Hypothesis DLN : Z.of_nat (length nb') = N' / 65536 + 1.
  Hypothesis DWN : Forall (fun b => 0x65f000 <= b /\ b + 2^20 <= ACEIL /\ b mod 4096 = 0) nb'.
  Hypothesis DLB : Z.of_nat (length bl') = (tf' + 2^20 - 1) / 2^20.
  Hypothesis DWB : Forall (fun b => 0x65f000 <= b /\ b + 2^23 <= ACEIL /\ b mod 4096 = 0) bl'.
  Hypothesis DLNB : Z.of_nat (length nb') <= 32768.
  Hypothesis DLBB : Z.of_nat (length bl') <= 4096.

  Let CS16 : class_size c mod 16 = 0 := class_size_mod16 c ltac:(lia).
  Let CSP : 32 <= class_size c := class_size_pos c ltac:(lia).

  #[using="hAR k n N' tf' nb' bl' GC HK EAB NB CS16"] Lemma pop_compact : compact L c AB = q.
  Proof.
    rewrite EAB, compact_chunk_at by exact CS16. destruct HK as [_ E].
    pose proof (Z.div_mod (class_size c) 16 ltac:(lia)) as D. rewrite CS16, Z.add_0_r in D. nia.
  Qed.

  #[using="NE HQ"] Lemma pop_split : pc_chunks p = removelast (pc_chunks p) ++ [q].
  Proof. rewrite HQ, <- last_nth by exact NE. apply app_removelast_last. exact NE. Qed.

  #[using="Type"] Lemma chunk_set_pop : forall c', chunk_set pop_h c' = (if c' =? c then compact L c AB :: chunk_set h c' else chunk_set h c').
  Proof.
    intros c'. unfold chunk_set. cbn [h_chunks pop_h h_L filter ck_prim ck_cls newk andb].
    rewrite (Z.eqb_sym c c'). destruct (Z.eqb_spec c' c) as [->|NEQ]; reflexivity.
  Qed.

  #[using="Type"] Lemma cache_set_pop : forall c', cache_set pop_h c' = (if c' =? c then removelast (pc_chunks p) else cache_set h c').
  Proof. intros c'. unfold cache_set. cbn [h_cache pop_h]. unfold pop_cache. destruct (c' =? c); reflexivity. Qed.

  #[using="hAR q k GC NE HQ HK EAB NB CS16"] Lemma owned_pop : forall c', owned pop_h c' = owned h c'.
  Proof.
    intros c'. unfold owned. rewrite cache_set_pop, chunk_set_pop.
    change (fa_set pop_h c') with (fa_set h c'). change (batch_set pop_h c') with (batch_set h c').
    destruct (Z.eqb_spec c' c) as [->|NEQ]; [| reflexivity].
    rewrite pop_compact. unfold cache_set. fold p. set (rl := removelast (pc_chunks p)).
    rewrite pop_split. fold rl. rewrite <- !app_assoc. reflexivity.
  Qed.

  #[using="Type"] Lemma blocks_pop : blocks pop_h = (AB + rz_size n, n) :: blocks h.
  Proof. unfold blocks, live. cbn [h_chunks pop_h filter ck_st newk]. reflexivity. Qed.

  
  (* [comment removed for export] *)
  #[using="N' tf' nb' bl' GC NB FP EC OLDAP"] Lemma hdr_new_old : forall k', In k' (h_chunks h) -> wf_chunk' h k' -> ck_hdr newk <> ck_hdr k'.
  Proof.
    intros k' Hk' W E. pose proof (hdr_in_slot h k' W) as [S1 S2]. pose proof (proj1 (Forall_forall _ _) OLDAP k' Hk') as AP. cbn beta in AP.
    unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize in E. cbn [ck_ab ck_n newk] in E.
    pose proof (rz_size_bound' n) as RZ.
    pose proof (needed_le_class n ltac:(lia) FP) as NC. rewrite EC in NC. unfold needed in NC. pose proof (rounded_spec n ltac:(lia)) as [R _].
    unfold ck_hdr, ck_user, ck_rz, kChunkHeaderSize in S1, S2. lia.
  Qed.

  #[using="q k AWF GC NE XC24 HQ HK EAB NB FP EC OLDAP DN DTF DLN DWN DLB DWB DLNB DLBB CS16"] Theorem awf'_pop : awf' pop_h.
  Proof.
    dpose AWF as (WL & WC & WR & (WKF & WKND & WKSEC) & WQ & WS & WD & WB & WBIG & WX & WG).
    assert (LEN : length (pc_chunks p) = (length (removelast (pc_chunks p)) + 1)%nat).
    { rewrite pop_split at 1. rewrite length_app. cbn [length]. reflexivity. }
    split; [exact WL|].
    split. { (* [comment removed for export] *)
      intros c' Hc'. pose proof (WC c' Hc') as X. cbn zeta in X |- *. cbn [h_cache h_cinit pop_h]. unfold pop_cache.
      change (carved pop_h c') with (carved h c').
      destruct (Z.eqb_spec c' c) as [->|NEQ]; [| exact X].
      fold p in X |- *. cbn [pc_max pc_csize pc_chunks]. ddestruct X as (X1 & X2 & X3 & X4 & X5).
      unfold pc_count in *. cbn [pc_chunks].
      split; [exact X1|]. split; [intros; lia|]. split; [lia|]. split; [lia|].
      rewrite pop_split in X5. apply Forall_app in X5 as [X5 _]. exact X5. }
    split. { (* [comment removed for export] *)
      intros c' Hc'. pose proof (WR c' Hc') as X. cbn zeta in X |- *.
      change (h_reg pop_h c') with (h_reg h c'). change (carved pop_h c') with (carved h c'). rewrite (owned_pop c'). exact X. }
    split. { (* [comment removed for export] *)
      split; [| split].
      - constructor.
        + unfold wf_chunk'. cbn [ck_n ck_st ck_prim ck_cls ck_ab newk]. change (carved pop_h c) with (carved h c). change (h_L pop_h) with L.
          split; [lia|]. split; [left; reflexivity|]. split; [symmetry; exact FP|].
          split; [symmetry; exact EC|]. split; [exact GC|]. exists k. split; [exact (proj1 HK)| exact EAB].
        + change (Forall (wf_chunk' h) (h_chunks h)). exact WKF.
      - cbn [map h_chunks pop_h ck_ab newk]. constructor; [| exact WKND].
        intros HIN. apply in_map_iff in HIN. ddestruct HIN as (k' & E & Hk').
        pose proof (proj1 (Forall_forall _ _) OLDAP k' Hk') as AP. cbn beta in AP.
        pose proof (proj1 (Forall_forall _ _) WKF k' Hk') as W. pose proof (hdr_in_slot h k' W) as [S1 S2].
        unfold ck_hdr, ck_user, ck_rz, ck_map_beg, kChunkHeaderSize in *. pose proof (rz_size_bound' (ck_n k')).
        destruct (ck_prim k'); lia.
      - intros i sh Hi. ddestruct (WKSEC i sh Hi) as (k' & Hk' & REST). exists k'. split; [right; exact Hk'| exact REST]. }
    split. { (* [comment removed for export] *)
      assert (FB : forall b, wf_batch h b -> wf_batch pop_h b).
      { (intros b dd_H; ddestruct dd_H as (B1 & B2 & B3 & B4)). unfold wf_batch. change (carved pop_h kBatchClass) with (carved h kBatchClass). change (h_L pop_h) with L.
        cbn [h_chunks pop_h]. split; [exact B1|]. split; [| split].
        - rewrite B2. f_equal. f_equal. apply map_ext_in. intros e He. cbn [find].
          destruct (Z.eqb_spec (ck_hdr newk) e) as [E|NEQ]; [| reflexivity].
          exfalso. destruct (proj1 (Forall_forall _ _) B3 e He) as (k0 & Hk0 & _ & Hh). apply (hdr_new_old k0 Hk0 (proj1 (Forall_forall _ _) WKF k0 Hk0)). congruence.
        - apply Forall_forall. intros e He. destruct (proj1 (Forall_forall _ _) B3 e He) as (k0 & Hk0 & R). exists k0. split; [right; exact Hk0| exact R].
        - exact B4. }
      ddestruct WQ as ((T1 & T2 & T3) & (G1 & G2 & G3) & ND & UQ).
      split; [split; [| split; [exact T2| exact T3]]| split; [split; [| split; [exact G2| exact G3]]| split; [exact ND|]]].
      - apply Forall_forall. intros b Hb. apply FB. exact (proj1 (Forall_forall _ _) T1 b Hb).
      - apply Forall_forall. intros b Hb. apply FB. exact (proj1 (Forall_forall _ _) G1 b Hb).
      - intros k0 [<-|Hk0] ST; [cbv in ST; discriminate ST|]. exact (UQ k0 Hk0 ST). }
    split; [exact WS|].
    split. { (* [comment removed for export] *)
      ddestruct WD as (N1 & _ & _ & T0 & _). unfold wf_depot'. cbn [h_dep pop_h d_n d_nb s_total d_bl h_havol]. unfold kDepotNodesL2 in *.
      repeat split; try assumption; lia. }
    split. { (* [comment removed for export] *) ddestruct WB as (F1 & F2 & F3). split; [exact F1|]. cbn [h_havol pop_h]. change (SECC pop_h) with (SECC h). lia. }
    split; [exact WBIG|]. split; [| exact WG].
    ddestruct WX as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9).
    split; [exact X1|]. split; [exact X2|]. split; [exact X3|]. split; [exact X4|]. split; [exact X5|]. split; [exact X6|]. split; [exact X7|]. split; [exact X8|].
    (* [comment removed for export] *)
    rewrite blocks_pop, cnt24_cons. cbn [snd]. destruct (win24 n) eqn:W; [pose proof (XC24 eq_refl) as B; clear - B; lia| clear - X9; lia].
  Qed.
End Pop.

(* [comment removed for export] *)
#[using="Type"] Lemma tf_after_put : ltac2:(CDefT.buildp (gd_tbl_APop ()) "Ph,$11.Pd,$12.Ptf',$12.P,(13.(14.(15.R3.)(14.R2.+3.))$16.)P,(13.=R3.)P,(13.=(17.(18.R5.)))P,(19.(13.(17.(18.R6.))R4.)(13.R4.(14.(17.(18.R6.))(1:.+2.(14.R5.+3.)))))P,(13.(1;.R5.)(14.(1;.(17.(18.R7.)))(14.R6.+3.)))(13.(14.R6.(1<.+2.+14.))(1<.+2.+20.))")
(* [comment removed for export] *).
Proof.
  intros h d tf' HF D0 T0 TB SF. unfold hfr, FR_MAXm, sframes in *.
  set (tf := s_total (h_dep h)) in *.
  pose proof (Z.div_mod tf (2^20) ltac:(lia)) as D1. pose proof (Z.mod_pos_bound tf (2^20) ltac:(lia)) as M1.
  pose proof (Z.div_mod tf' (2^20) ltac:(lia)) as D2. pose proof (Z.mod_pos_bound tf' (2^20) ltac:(lia)) as M2.
  assert (A1 : tf - 31 * (tf / 2^20) + d <= 2^32 - 2^21) by lia.
  assert (A2 : tf / 2^20 <= 4200) by lia.
  assert (A3 : tf <= 2^32) by lia.
  assert (A4 : tf' <= 3 * 2^32) by lia.
  assert (A5 : tf' / 2^20 <= 12288) by lia.
  lia.
Qed.


End ARUN_1.
