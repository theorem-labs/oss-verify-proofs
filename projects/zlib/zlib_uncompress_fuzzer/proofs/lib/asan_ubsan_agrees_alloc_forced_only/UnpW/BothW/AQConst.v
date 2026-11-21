(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith Lia.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Spec Require Import AsanCtrl.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.UnpW.BothW Require Import ABase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section CANSEC1. Context {rc : runConstT}.
Definition AQUAR_Q : Z := 0xd67f0.               (* [comment removed for export] *)
Definition AQ_MAX : Z := 0xd6830.                (* [comment removed for export] *)
Definition AQ_MIN : Z := 0xd6838.                (* [comment removed for export] *)
Definition AQ_MAXC : Z := 0xd6840.               (* [comment removed for export] *)
Definition AQ_MUTEX : Z := 0xd6888.              (* [comment removed for export] *)
Definition AQ_GCACHE : Z := 0xd6890.             (* [comment removed for export] *)
Definition aq_tcache (L : alayout) : Z := al_t L + 80.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition AIA_BASE : Z := 0xdad80.              (* [comment removed for export] *)
Definition AIA_SIZE : Z := 0x81030.               (* [comment removed for export] *)
Definition AIA_MAP1 : Z := 0xdad88.              (* [comment removed for export] *)
Definition AIA_MAP1_LEN : Z := 0x40000.
Definition AIA_FLAG : Z := 0x169608.              (* [comment removed for export] *)
Definition AFHOOK : Z := 0x16b648.                (* [comment removed for export] *)
End CANSEC1.

(* [comment removed for export] *)
Definition qsz (lst : Z) : Z := if lst =? 0 then 8 else 8192.
Arguments qsz : simpl never.
Lemma qsz_0 : qsz 0 = 8.
Proof. reflexivity. Qed.
Lemma qsz_eq0 : forall lst, lst = 0 -> qsz lst = 8.
Proof. intros lst ->. reflexivity. Qed.
Lemma qsz_nz : forall lst, lst <> 0 -> qsz lst = 8192.
Proof. intros lst H. unfold qsz. destruct (Z.eqb_spec lst 0); [contradiction| reflexivity]. Qed.
Lemma qsz_pos : forall lst, 0 < lst -> qsz lst = 8192.
Proof. intros lst H. apply qsz_nz. lia. Qed.
Lemma qsz_bound : forall lst, 8 <= qsz lst <= 8192.
Proof. intros lst. unfold qsz. destruct (lst =? 0); lia. Qed.
(* [comment removed for export] *)
Lemma qsz_int : forall lst, 0 <= lst -> lst < 18446744073709551616 ->
  exists z, 0 <= z <= 1 /\ qsz lst = 8 + 8184 * z /\ z <= lst /\ lst <= 18446744073709551616 * z.
Proof.
  intros lst H0 H1. unfold qsz. destruct (Z.eqb_spec lst 0) as [E|NE]; [exists 0| exists 1]; lia.
Qed.
