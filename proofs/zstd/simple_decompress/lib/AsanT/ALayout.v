(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import AsanCtrl.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition al_res (L : alayout) : Z := 4096 * al_V L 221%nat.
(* [comment removed for export] *)
Definition al_dtls (L : alayout) : Z := 4096 * al_V L 323%nat.
End CANSEC1.
Notation ARES_LEN := 137439023104 (only parsing).   (* [comment removed for export] *)
Notation AOBJ_LO := 17594333499392 (only parsing).  (* [comment removed for export] *)

Section CANSEC2. Context {rc : runConstT}.
Definition adisj (a1 n1 a2 n2 : Z) : Prop := a1 + n1 <= a2 \/ a2 + n2 <= a1.
(* [comment removed for export] *)
Definition aobj (a n : Z) : Prop := a mod 4096 = 0 /\ 4096 <= a /\ a + n <= ATOP /\ sclr a n /\ iclr a n.
Lemma aobj_img : forall a n, aobj a n -> 0x10000 <= n -> AIMG_HI <= a.
Proof. intros a n (_ & H1 & _ & _ & H4) Hn. unfold iclr, AIMG_LO, AIMG_HI in *. lia. Qed.

Record alayout_ok (L : alayout) : Prop := mkALO {
  ao_t : aobj (al_t L) 4096;  ao_ctx : aobj (al_ctx L) 65536;  ao_nodes : aobj (al_nodes L) 1048576;
  ao_store : aobj (al_store L) 8388608;  ao_fake : aobj (al_fake L) 11571200;  ao_res : aobj (al_res L) 137439023104;
  ao_ptr : aobj (al_ptr_array L) 8388608;  ao_dtls : aobj (al_dtls L) 4096;
  ao_res_hi : 0x10007fff8000 <= al_res L;     (* [comment removed for export] *)
  (* [comment removed for export] *)
  ao_space : al_res L + 4096 <= al_space_beg L <= al_res L + 65536;  ao_space_al : al_space_beg L mod 65536 = 0;
  (* [comment removed for export] *)
  ad_t_res : adisj (al_t L) 4096 (al_res L) 137439023104;  ad_ctx_res : adisj (al_ctx L) 65536 (al_res L) 137439023104;
  ad_nodes_res : adisj (al_nodes L) 1048576 (al_res L) 137439023104;  ad_store_res : adisj (al_store L) 8388608 (al_res L) 137439023104;
  ad_fake_res : adisj (al_fake L) 11571200 (al_res L) 137439023104;  ad_ptr_res : adisj (al_ptr_array L) 8388608 (al_res L) 137439023104;
  ad_t_ctx : adisj (al_t L) 4096 (al_ctx L) 65536;  ad_t_nodes : adisj (al_t L) 4096 (al_nodes L) 1048576;
  ad_t_store : adisj (al_t L) 4096 (al_store L) 8388608;  ad_t_fake : adisj (al_t L) 4096 (al_fake L) 11571200;
  ad_t_ptr : adisj (al_t L) 4096 (al_ptr_array L) 8388608;
  ad_ctx_nodes : adisj (al_ctx L) 65536 (al_nodes L) 1048576;  ad_ctx_store : adisj (al_ctx L) 65536 (al_store L) 8388608;
  ad_ctx_fake : adisj (al_ctx L) 65536 (al_fake L) 11571200;  ad_ctx_ptr : adisj (al_ctx L) 65536 (al_ptr_array L) 8388608;
  ad_nodes_store : adisj (al_nodes L) 1048576 (al_store L) 8388608;  ad_nodes_fake : adisj (al_nodes L) 1048576 (al_fake L) 11571200;
  ad_nodes_ptr : adisj (al_nodes L) 1048576 (al_ptr_array L) 8388608;
  ad_store_fake : adisj (al_store L) 8388608 (al_fake L) 11571200;  ad_store_ptr : adisj (al_store L) 8388608 (al_ptr_array L) 8388608;
  ad_fake_ptr : adisj (al_fake L) 11571200 (al_ptr_array L) 8388608;
  ad_dtls_res : adisj (al_dtls L) 4096 (al_res L) 137439023104;  ad_t_dtls : adisj (al_t L) 4096 (al_dtls L) 4096;
  ad_ctx_dtls : adisj (al_ctx L) 65536 (al_dtls L) 4096;  ad_nodes_dtls : adisj (al_nodes L) 1048576 (al_dtls L) 4096;
  ad_store_dtls : adisj (al_store L) 8388608 (al_dtls L) 4096;  ad_fake_dtls : adisj (al_fake L) 11571200 (al_dtls L) 4096;
  ad_dtls_ptr : adisj (al_dtls L) 4096 (al_ptr_array L) 8388608;
  (* [comment removed for export] *)
  ao_stack : al_bot L + 0x800000 = al_top L /\ al_top L mod 4096 = 0 /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936);
  ao_U : (length (al_U L) <= Z.to_nat AUMAX)%nat
}.

(* [comment removed for export] *)
Lemma alayout_space : forall L, alayout_ok L ->
  0x10007fff8000 <= al_space_beg L /\ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= ATOP /\ al_space_beg L mod K_ALIGN = 0
  /\ 0 <= al_space_beg L < 2^47.
Proof.
  intros L H. pose proof (ao_res L H) as R. pose proof (ao_res_hi L H) as RH. pose proof (ao_space L H) as SB. pose proof (ao_space_al L H) as SAL.
  unfold aobj, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. change (2^37) with 137438953472. lia.
Qed.

(* [comment removed for export] *)
Lemma alayout_slot_disj : forall L A sz, alayout_ok L ->
  al_space_beg L <= A -> A + sz <= al_space_beg L + K_SPACE_SIZE -> 0 <= sz ->
     (al_t L + 4096 <= A \/ A + sz <= al_t L)
  /\ (al_ctx L + 65536 <= A \/ A + sz <= al_ctx L)
  /\ (al_nodes L + 1048576 <= A \/ A + sz <= al_nodes L)
  /\ (al_store L + 8388608 <= A \/ A + sz <= al_store L)
  /\ (al_fake L + 11571200 <= A \/ A + sz <= al_fake L).
Proof.
  intros L A sz H LO HI SZ. pose proof (ao_space L H) as SB. unfold K_SPACE_SIZE in HI. change (2^37) with 137438953472 in HI.
  unfold adisj in *.
  split; [pose proof (ad_t_res L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_ctx_res L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_nodes_res L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_store_res L H) as D; unfold adisj in D; lia|].
  pose proof (ad_fake_res L H) as D; unfold adisj in D; lia.
Qed.

(* [comment removed for export] *)
Lemma alayout_t : forall L, alayout_ok L ->
  sclr (al_t L) 4096 /\ al_t L + 4096 <= ATOP /\ al_t L mod 4096 = 0 /\ iclr (al_t L) 4096.
Proof. intros L H. pose proof (ao_t L H) as T. unfold aobj in *. tauto. Qed.
Lemma alayout_t_lin : forall L, alayout_ok L -> 4096 <= al_t L /\ al_t L + 4096 <= ATOP.
Proof. intros L H. pose proof (ao_t L H) as T. unfold aobj in *. tauto. Qed.
Lemma alayout_ctx : forall L, alayout_ok L ->
  sclr (al_ctx L) 65536 /\ al_ctx L + 65536 <= ATOP /\ AIMG_HI <= al_ctx L /\ 0 < al_ctx L
  /\ (al_ctx L + 4096 <= al_t L \/ al_t L + 4096 <= al_ctx L).
Proof.
  intros L H. pose proof (ao_ctx L H) as C. pose proof (aobj_img _ _ C ltac:(lia)) as CI. pose proof (ad_t_ctx L H) as D.
  unfold aobj, adisj, AIMG_HI in *. repeat split; try tauto; lia.
Qed.
Lemma alayout_depot : forall L, alayout_ok L ->
  sclr (al_nodes L) 1048576 /\ al_nodes L + 1048576 <= ATOP /\ AIMG_HI <= al_nodes L
  /\ sclr (al_store L) 8388608 /\ al_store L + 8388608 <= ATOP /\ AIMG_HI <= al_store L
  /\ (al_t L + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= al_t L) /\ (al_t L + 4096 <= al_store L \/ al_store L + 8388608 <= al_t L)
  /\ (al_ctx L + 4096 <= al_nodes L \/ al_nodes L + 1048576 <= al_ctx L) /\ (al_ctx L + 4096 <= al_store L \/ al_store L + 8388608 <= al_ctx L).
Proof.
  intros L H. pose proof (ao_nodes L H) as N. pose proof (ao_store L H) as S.
  pose proof (aobj_img _ _ N ltac:(lia)) as NI. pose proof (aobj_img _ _ S ltac:(lia)) as SI. unfold aobj, AIMG_HI in *.
  split; [tauto|]. split; [lia|]. split; [lia|]. split; [tauto|]. split; [lia|]. split; [lia|].
  split; [pose proof (ad_t_nodes L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_t_store L H) as D; unfold adisj in D; lia|].
  split; [pose proof (ad_ctx_nodes L H) as D; unfold adisj in D; lia|].
  pose proof (ad_ctx_store L H) as D; unfold adisj in D; lia.
Qed.
(* [comment removed for export] *)
Lemma alayout_stack : forall L, alayout_ok L ->
  al_bot L + 0x800000 = al_top L /\ al_top L <= 2^47 /\ (ATOP - 160 <= al_bot L <= ATOP + 3936).
Proof. intros L H. pose proof (ao_stack L H). lia. Qed.
(* [comment removed for export] *)
Lemma alayout_page_bot : forall L, alayout_ok L -> forall e, e mod 4096 = 0 -> e <= ATOP -> e <= al_bot L.
Proof. intros L H e He Hle. pose proof (ao_stack L H) as (S1 & S2 & S3 & S4). Z.div_mod_to_equations. nia. Qed.
End CANSEC2.
