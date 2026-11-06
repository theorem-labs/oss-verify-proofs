(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require PropExec__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StoreOk. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StreamSim__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require MmapSim. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require RefLayout__Common. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common Require StepTac. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StreamSim__Common.StreamSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib Require Import StdioSymDrive.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Img. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3Syms__A3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3 Require A3RW__A3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3RW__A3.A3RW.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma fetch_set_tid_ecall : fetch_word SEGS (Z_to_bv 64 A_set_tid_ecall) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition fetchd (a : Z) : option (instr * Z) :=
  match fetch_word SEGS (Z_to_bv 64 a) with Some w => if is_ecall w then None else decode_any w | None => None end.

Lemma envloop_code_0 : fetchd A_envloop = Some (Load SZ8 true 10 9 0, 4).          Proof. vm_refl_bv. Qed.
Lemma envloop_code_4 : fetchd (A_envloop + 4) = Some (OpImm ALU_ADD 9 9 8, 4).      Proof. vm_refl_bv. Qed.
Lemma envloop_code_8 : fetchd (A_envloop + 8) = Some (Branch BC_NE 10 0 8184, 4).  Proof. vm_refl_bv. Qed.
Lemma envloop_exit_eq : A_envloop_exit = A_envloop + 12.                           Proof. reflexivity. Qed.

Lemma pnloop_code_m8 : fetchd (A_pnloop - 8) = Some (Store SZ8 10 11 0, 4).          Proof. vm_refl_bv. Qed.
Lemma pnloop_code_m4 : fetchd (A_pnloop - 4) = Some (OpImm ALU_ADD 11 11 1, 4).      Proof. vm_refl_bv. Qed.
Lemma pnloop_code_0 : fetchd A_pnloop = Some (Load SZ1 false 13 11 4095, 4).         Proof. vm_refl_bv. Qed.
Lemma pnloop_code_4 : fetchd (A_pnloop + 4) = Some (Branch BC_EQ 13 12 8180, 4).    Proof. vm_refl_bv. Qed.
Lemma pnloop_code_8 : fetchd (A_pnloop + 8) = Some (Branch BC_NE 13 0 8180, 4).     Proof. vm_refl_bv. Qed.
Lemma pnloop_exit_eq : A_pnloop_exit = A_pnloop + 12.                              Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ssp_sb_code : fetchd A_ssp_sb = Some (Store SZ1 10 0 1, 4).                      Proof. vm_refl_bv. Qed.
Lemma ssp_ld_code : fetchd A_ssp_ld = Some (Load SZ8 true 10 10 0, 4).                Proof. vm_refl_bv. Qed.
Lemma ssp_sb_next : A_ssp_ld = A_ssp_sb + 4.                                         Proof. reflexivity. Qed.
Lemma ssp_ld_next : A_ssp_after_ld = A_ssp_ld + 4.                                   Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fetchd_some : forall a i, fetchd a = Some i ->
  exists w, fetch_word SEGS (Z_to_bv 64 a) = Some w /\ is_ecall w = false /\ decode_any w = Some i.
Proof.
  intros a i H. unfold fetchd in H.
  destruct (fetch_word SEGS (Z_to_bv 64 a)) as [w|]; [|discriminate].
  exists w. destruct (is_ecall w); [discriminate|]. auto.
Qed.

Lemma img_hull : 0 <= A_img_lo <= A_img_hi /\ A_img_hi <= 2 ^ 32.
Proof. unfold A_img_lo, A_img_hi. lia. Qed.

(* [comment removed for export] *)
Lemma rw_window :
  (0 <= A_rw_lo /\ 0 <= A_rw_len /\ A_rw_lo + A_rw_len < 2 ^ 64)
  /\ forall m (x : word), A_rw_lo <= bv_unsigned x < A_rw_lo + A_rw_len -> wview SEGS m x <> None.
Proof.
  split; [unfold A_rw_lo, A_rw_len; lia|].
  intros m x Hx. apply rw_window_img. unfold RW_LO, IMG_HI, A_rw_lo, A_rw_len in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_store_ok : forall m (a : word) n,
  A_rw_lo <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= A_rw_lo + A_rw_len -> store_ok SEGS m a n = true.
Proof.
  intros m a n Hl Hh. apply store_ok_of_all; [unfold A_rw_lo, A_rw_len in *; lia|].
  intros x Hx. apply rw_window_img. unfold RW_LO, IMG_HI, A_rw_lo, A_rw_len in *. lia.
Qed.

Lemma rw_in_hull : A_img_lo <= A_rw_lo /\ A_rw_lo + A_rw_len <= A_img_hi.
Proof. unfold A_img_lo, A_img_hi, A_rw_lo, A_rw_len. lia. Qed.

(* [comment removed for export] *)
Definition reservedZ : list (Z * Z) :=
  List.map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (segments_reserved SEGS).

Fixpoint tiles (lo hi : Z) (l : list (Z * Z)) : bool :=
  match l with
  | [] => Z.eqb lo hi
  | (b, s) :: r => Z.eqb b lo && Z.leb 0 s && tiles (lo + s) hi r
  end.

Lemma reserved_tiles : tiles A_img_lo A_img_hi reservedZ = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tiles_apart : forall l lo hi (a n : Z),
  tiles lo hi (List.map (fun p : word * word => (bv_unsigned (fst p), bv_unsigned (snd p))) l) = true ->
  0 < n -> 0 <= a -> a + n < 2 ^ 64 ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  (a + n <= lo \/ hi <= a) \/ lo = hi.
Proof.
  induction l as [|[b s] r IH]; intros lo hi a n Ht Hn Ha Hnw Hrf; cbn [tiles List.map fst snd] in Ht.
  - apply Z.eqb_eq in Ht. right. exact Ht.
  - apply andb_prop in Ht as [Ht Hr]. apply andb_prop in Ht as [Hb Hs].
    apply Z.eqb_eq in Hb. apply Z.leb_le in Hs.
    apply region_free_cons in Hrf as [D Hrf]. rewrite !u64_lit in D by lia.
    pose proof (IH (lo + bv_unsigned s) hi a n Hr Hn Ha Hnw Hrf) as IH'. lia.
Qed.

Lemma reserved_apart : forall (a : word) (n : Z),
  0 < n -> bv_unsigned a + n < 2 ^ 64 ->
  region_free (segments_reserved SEGS) a (Z_to_bv 64 n) = true ->
  bv_unsigned a + n <= A_img_lo \/ A_img_hi <= bv_unsigned a.
Proof.
  intros a n Hn Hnw Hrf. pose proof (u64_range a) as Ha.
  assert (Hlt : A_img_lo < A_img_hi) by (unfold A_img_lo, A_img_hi; lia).
  rewrite <- (Z_to_bv_bv_unsigned 64 a) in Hrf.
  destruct (tiles_apart (segments_reserved SEGS) A_img_lo A_img_hi (bv_unsigned a) n reserved_tiles Hn ltac:(lia) Hnw Hrf) as [H|H]; [exact H | lia].
Qed.

Lemma reserved_small :
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (segments_reserved SEGS).
Proof.
  assert (E : forallb (fun p => Z.leb (bv_unsigned (snd p)) (2 ^ 30)) (segments_reserved SEGS) = true)
    by (vm_compute; reflexivity).
  apply Forall_forall. intros p Hp. apply Z.leb_le. exact (proj1 (forallb_forall _ _) E p Hp).
Qed.

Lemma reserved_count : Z.of_nat (length (segments_reserved SEGS)) <= 1000.
Proof. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Lemma fetch_internal_mmap_ecall : fetch_word SEGS (Z_to_bv 64 A_internal_mmap_ecall) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

Definition JSELF : bv 32 := 0x0000006f.   (* [comment removed for export] *)
Lemma decode_JSELF : decode_any JSELF = Some (Jal 0 0, 4).   Proof. vm_refl_bv. Qed.
Lemma is_ecall_JSELF : is_ecall JSELF = false.                Proof. reflexivity. Qed.
Lemma fetch_spin_shadow0 : fetch_word SEGS (Z_to_bv 64 A_spin_shadow0) = Some JSELF. Proof. vm_refl_bv. Qed.
Lemma fetch_spin_shadow1 : fetch_word SEGS (Z_to_bv 64 A_spin_shadow1) = Some JSELF. Proof. vm_refl_bv. Qed.
Lemma fetch_spin_shadow2 : fetch_word SEGS (Z_to_bv 64 A_spin_shadow2) = Some JSELF. Proof. vm_refl_bv. Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3 Require A3RW.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.PropExec__Common.PropExec OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StoreOk OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StreamSim__Common.StreamSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.MmapSim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.RefLayout__Common.AgentLib OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Common.StepTac.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.Lib.StdioSymDrive.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Img.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3Syms.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.A3.A3Syms__A3.A3SymsBoot.TwB. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.B3.A3RW.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma fetch_set_tid_ecall : fetch_word SEGS (Z_to_bv 64 A_set_tid_ecall) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition fetchd (a : Z) : option (instr * Z) :=
  match fetch_word SEGS (Z_to_bv 64 a) with Some w => if is_ecall w then None else decode_any w | None => None end.

Lemma envloop_code_0 : fetchd A_envloop = Some (Load SZ8 true 10 9 0, 4).          Proof. vm_refl_bv. Qed.
Lemma envloop_code_4 : fetchd (A_envloop + 4) = Some (OpImm ALU_ADD 9 9 8, 4).      Proof. vm_refl_bv. Qed.
Lemma envloop_code_8 : fetchd (A_envloop + 8) = Some (Branch BC_NE 10 0 8184, 4).  Proof. vm_refl_bv. Qed.
Lemma envloop_exit_eq : A_envloop_exit = A_envloop + 12.                           Proof. reflexivity. Qed.

Lemma pnloop_code_m8 : fetchd (A_pnloop - 8) = Some (Store SZ8 10 11 0, 4).          Proof. vm_refl_bv. Qed.
Lemma pnloop_code_m4 : fetchd (A_pnloop - 4) = Some (OpImm ALU_ADD 11 11 1, 4).      Proof. vm_refl_bv. Qed.
Lemma pnloop_code_0 : fetchd A_pnloop = Some (Load SZ1 false 13 11 4095, 4).         Proof. vm_refl_bv. Qed.
Lemma pnloop_code_4 : fetchd (A_pnloop + 4) = Some (Branch BC_EQ 13 12 8180, 4).    Proof. vm_refl_bv. Qed.
Lemma pnloop_code_8 : fetchd (A_pnloop + 8) = Some (Branch BC_NE 13 0 8180, 4).     Proof. vm_refl_bv. Qed.
Lemma pnloop_exit_eq : A_pnloop_exit = A_pnloop + 12.                              Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ssp_sb_code : fetchd A_ssp_sb = Some (Store SZ1 10 0 1, 4).                      Proof. vm_refl_bv. Qed.
Lemma ssp_ld_code : fetchd A_ssp_ld = Some (Load SZ8 true 10 10 0, 4).                Proof. vm_refl_bv. Qed.
Lemma ssp_sb_next : A_ssp_ld = A_ssp_sb + 4.                                         Proof. reflexivity. Qed.
Lemma ssp_ld_next : A_ssp_after_ld = A_ssp_ld + 4.                                   Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma fetchd_some : forall a i, fetchd a = Some i ->
  exists w, fetch_word SEGS (Z_to_bv 64 a) = Some w /\ is_ecall w = false /\ decode_any w = Some i.
Proof.
  intros a i H. unfold fetchd in H.
  destruct (fetch_word SEGS (Z_to_bv 64 a)) as [w|]; [|discriminate].
  exists w. destruct (is_ecall w); [discriminate|]. auto.
Qed.

Lemma img_hull : 0 <= A_img_lo <= A_img_hi /\ A_img_hi <= 2 ^ 32.
Proof. unfold A_img_lo, A_img_hi. lia. Qed.

(* [comment removed for export] *)
Lemma rw_window :
  (0 <= A_rw_lo /\ 0 <= A_rw_len /\ A_rw_lo + A_rw_len < 2 ^ 64)
  /\ forall m (x : word), A_rw_lo <= bv_unsigned x < A_rw_lo + A_rw_len -> wview SEGS m x <> None.
Proof.
  split; [unfold A_rw_lo, A_rw_len; lia|].
  intros m x Hx. apply rw_window_img. unfold RW_LO, IMG_HI, A_rw_lo, A_rw_len in *. lia.
Qed.

(* [comment removed for export] *)
Lemma rw_store_ok : forall m (a : word) n,
  A_rw_lo <= bv_unsigned a -> bv_unsigned a + Z.of_nat n <= A_rw_lo + A_rw_len -> store_ok SEGS m a n = true.
Proof.
  intros m a n Hl Hh. apply store_ok_of_all; [unfold A_rw_lo, A_rw_len in *; lia|].
  intros x Hx. apply rw_window_img. unfold RW_LO, IMG_HI, A_rw_lo, A_rw_len in *. lia.
Qed.

Lemma rw_in_hull : A_img_lo <= A_rw_lo /\ A_rw_lo + A_rw_len <= A_img_hi.
Proof. unfold A_img_lo, A_img_hi, A_rw_lo, A_rw_len. lia. Qed.

(* [comment removed for export] *)
Definition reservedZ : list (Z * Z) :=
  List.map (fun p => (bv_unsigned (fst p), bv_unsigned (snd p))) (segments_reserved SEGS).

Fixpoint tiles (lo hi : Z) (l : list (Z * Z)) : bool :=
  match l with
  | [] => Z.eqb lo hi
  | (b, s) :: r => Z.eqb b lo && Z.leb 0 s && tiles (lo + s) hi r
  end.

Lemma reserved_tiles : tiles A_img_lo A_img_hi reservedZ = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tiles_apart : forall l lo hi (a n : Z),
  tiles lo hi (List.map (fun p : word * word => (bv_unsigned (fst p), bv_unsigned (snd p))) l) = true ->
  0 < n -> 0 <= a -> a + n < 2 ^ 64 ->
  region_free l (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  (a + n <= lo \/ hi <= a) \/ lo = hi.
Proof.
  induction l as [|[b s] r IH]; intros lo hi a n Ht Hn Ha Hnw Hrf; cbn [tiles List.map fst snd] in Ht.
  - apply Z.eqb_eq in Ht. right. exact Ht.
  - apply andb_prop in Ht as [Ht Hr]. apply andb_prop in Ht as [Hb Hs].
    apply Z.eqb_eq in Hb. apply Z.leb_le in Hs.
    apply region_free_cons in Hrf as [D Hrf]. rewrite !u64_lit in D by lia.
    pose proof (IH (lo + bv_unsigned s) hi a n Hr Hn Ha Hnw Hrf) as IH'. lia.
Qed.

Lemma reserved_apart : forall (a : word) (n : Z),
  0 < n -> bv_unsigned a + n < 2 ^ 64 ->
  region_free (segments_reserved SEGS) a (Z_to_bv 64 n) = true ->
  bv_unsigned a + n <= A_img_lo \/ A_img_hi <= bv_unsigned a.
Proof.
  intros a n Hn Hnw Hrf. pose proof (u64_range a) as Ha.
  assert (Hlt : A_img_lo < A_img_hi) by (unfold A_img_lo, A_img_hi; lia).
  rewrite <- (Z_to_bv_bv_unsigned 64 a) in Hrf.
  destruct (tiles_apart (segments_reserved SEGS) A_img_lo A_img_hi (bv_unsigned a) n reserved_tiles Hn ltac:(lia) Hnw Hrf) as [H|H]; [exact H | lia].
Qed.

Lemma reserved_small :
  Forall (fun p => bv_unsigned (snd p) <= 2 ^ 30) (segments_reserved SEGS).
Proof.
  assert (E : forallb (fun p => Z.leb (bv_unsigned (snd p)) (2 ^ 30)) (segments_reserved SEGS) = true)
    by (vm_compute; reflexivity).
  apply Forall_forall. intros p Hp. apply Z.leb_le. exact (proj1 (forallb_forall _ _) E p Hp).
Qed.

Lemma reserved_count : Z.of_nat (length (segments_reserved SEGS)) <= 1000.
Proof. vm_compute. discriminate. Qed.

(* [comment removed for export] *)
Lemma fetch_internal_mmap_ecall : fetch_word SEGS (Z_to_bv 64 A_internal_mmap_ecall) = Some ECALLW.
Proof. vm_compute. reflexivity. Qed.

Definition JSELF : bv 32 := 0x0000006f.   (* [comment removed for export] *)
Lemma decode_JSELF : decode_any JSELF = Some (Jal 0 0, 4).   Proof. vm_refl_bv. Qed.
Lemma is_ecall_JSELF : is_ecall JSELF = false.                Proof. reflexivity. Qed.
Lemma fetch_spin_shadow0 : fetch_word SEGS (Z_to_bv 64 A_spin_shadow0) = Some JSELF. Proof. vm_refl_bv. Qed.
Lemma fetch_spin_shadow1 : fetch_word SEGS (Z_to_bv 64 A_spin_shadow1) = Some JSELF. Proof. vm_refl_bv. Qed.
Lemma fetch_spin_shadow2 : fetch_word SEGS (Z_to_bv 64 A_spin_shadow2) = Some JSELF. Proof. vm_refl_bv. Qed.
End TwB.
