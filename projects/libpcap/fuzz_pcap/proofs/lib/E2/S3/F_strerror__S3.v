(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Lia.
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Tac Bytes SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require StrerrorData.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ITree Nodes Decode.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Uaccess.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Arr.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem.
From Stdlib Require String.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Fmt Stdio.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require PcapPrelim PcapTypes PcapPure Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require KeepHyps.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Module F_strerror.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Bytes SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require StrerrorData. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.StrerrorData OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv ssegs _ |- _ => exact H end.

Definition strerror_entry := 0x1e45c%Z.
Definition strerror_r_entry := 0x20f74%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strerror_e (e : Z) : Z := if ((0 <=? e) && (e <? 132))%Z then e else 0.

(* [comment removed for export] *)
Definition strerror_tab : list byte := errmsgstr_bytes ++ errmsgidx_bytes.

(* [comment removed for export] *)
Definition sr_idx (k : Z) : Z :=
  bv_unsigned (zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn (Z.to_nat (2 * k)) errmsgidx_bytes))))).
Definition sr_res (k : Z) : Z := ERRMSGSTR + sr_idx k.
Definition sr_msgb (k : Z) : list byte := map (Z_to_bv 8) (nth (Z.to_nat k) strerror_msgZ []).
Definition sr_slack (k : Z) : list byte :=
  firstn 7 (skipn (Z.to_nat (sr_idx k) + length (sr_msgb k) + 1) strerror_tab).

Definition strerror_res (e : Z) : Z := sr_res (strerror_e e).
Definition strerror_msgb (e : Z) : list byte := sr_msgb (strerror_e e).
Definition strerror_slack (e : Z) : list byte := sr_slack (strerror_e e).

Example strerror_res_2 : strerror_res 2 = (0x11638 + 133)%Z. Proof. vm_compute. reflexivity. Qed.
Example strerror_res_neg : strerror_res (-7) = 0x11638%Z. Proof. vm_compute. reflexivity. Qed.
Example strerror_msgb_12 : map bv_unsigned (strerror_msgb 12) = [79; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121]%Z. (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.

Lemma strerror_e_range : forall e, (0 <= strerror_e e < 132)%Z.
Proof. intros e. unfold strerror_e. destruct (Z.leb_spec0 0 e), (Z.ltb_spec0 e 132); cbn; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errmsgidx_at : forall m, mem_inv ssegs m -> bytes_at ssegs m ERRMSGIDX errmsgidx_bytes.
Proof.
  intros m MI.
  pose proof (ro_cells_image ssegs m ERRMSGIDX errmsgidx_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold ERRMSGIDX; lia)
                ltac:(unfold errmsgidx_bytes, ERRMSGIDX; rewrite length_map; vm_compute (length errmsgidx_Z); lia)) as RO.
  apply ro_cells_bytes_at in RO. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma strerror_tab_at : forall m, mem_inv ssegs m -> bytes_at ssegs m ERRMSGSTR strerror_tab.
Proof.
  intros m MI.
  pose proof (ro_cells_image ssegs m ERRMSGSTR strerror_tab MI ltac:(vm_compute; reflexivity) ltac:(unfold ERRMSGSTR; lia)
                ltac:(unfold strerror_tab, errmsgstr_bytes, errmsgidx_bytes, ERRMSGSTR; rewrite length_app, !length_map;
                      vm_compute (length errmsgidx_Z); vm_compute (length errmsgstr_Z); lia)) as RO.
  apply ro_cells_bytes_at in RO. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma bytes_at_sub : forall m A l (i n : nat), bytes_at ssegs m A l -> (i + n <= length l)%nat ->
  bytes_at ssegs m (A + Z.of_nat i) (firstn n (skipn i l)).
Proof.
  intros m A l i n H Hl.
  rewrite <- (firstn_skipn i l) in H. apply (proj1 (bytes_at_app _ _ _ _ _)) in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn i l)) in H. apply (proj1 (bytes_at_app _ _ _ _ _)) in H. destruct H as [H _]. exact H.
Qed.

Lemma notin0_of_forallb : forall l : list byte,
  forallb (fun b => negb (bv_unsigned b =? 0)%Z) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H Hin. apply forallb_forall with (x := Z_to_bv 8 0) in H; [|exact Hin]. cbn in H. discriminate.
Qed.

Lemma Zcases_nat : forall (P : Z -> Prop) (n : nat),
  (forall k : nat, (k < n)%nat -> P (Z.of_nat k)) -> forall z, (0 <= z < Z.of_nat n)%Z -> P z.
Proof. intros P n H z Hz. replace z with (Z.of_nat (Z.to_nat z)) by lia. apply H. lia. Qed.

Local Ltac sr_case TAB :=
  lazymatch goal with |- bytes_at _ _ (sr_res (Z.of_nat ?k)) _ /\ _ =>
    let i := eval vm_compute in (Z.to_nat (sr_idx (Z.of_nat k))) in
    let n := eval vm_compute in (length (sr_msgb (Z.of_nat k)) + 8)%nat in
    split; [ replace (sr_res (Z.of_nat k)) with (ERRMSGSTR + Z.of_nat i)%Z by (vm_compute; reflexivity);
             replace (sr_msgb (Z.of_nat k) ++ Z_to_bv 8 0 :: sr_slack (Z.of_nat k)) with (firstn n (skipn i strerror_tab)) by (vm_compute; reflexivity);
             apply (bytes_at_sub _ _ _ i n TAB); vm_compute; lia
           | split; [ apply notin0_of_forallb; vm_compute; reflexivity | vm_compute; reflexivity ] ]
  end.

(* [comment removed for export] *)
Lemma bytes_eq_chk_s : forall l1 l2 : list byte, length l1 = length l2 ->
  forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p))) (combine l1 l2) = true -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] Hl H; cbn in *; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | apply IH; [lia | exact H2]].
Qed.

Lemma sr_msg_at : forall m k, mem_inv ssegs m -> (0 <= k < 132)%Z ->
  bytes_at ssegs m (sr_res k) (sr_msgb k ++ Z_to_bv 8 0 :: sr_slack k) /\ ~ In (Z_to_bv 8 0) (sr_msgb k) /\ length (sr_slack k) = 7%nat.
Proof.
  intros m k MI Hk. pose proof (strerror_tab_at m MI) as TAB.
  assert (ALL : forallb (fun j : nat =>
      let K := Z.of_nat j in let i := Z.to_nat (sr_idx K) in let n := (length (sr_msgb K) + 8)%nat in
      forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p)))
              (combine (sr_msgb K ++ Z_to_bv 8 0 :: sr_slack K) (firstn n (skipn i strerror_tab)))
      && Nat.eqb (length (sr_msgb K ++ Z_to_bv 8 0 :: sr_slack K)) (length (firstn n (skipn i strerror_tab)))
      && Nat.leb (i + n) (length strerror_tab)
      && forallb (fun b => negb (bv_unsigned b =? 0)%Z) (sr_msgb K)
      && Nat.eqb (length (sr_slack K)) 7
      && Z.eqb (sr_res K) (ERRMSGSTR + Z.of_nat i)) (seq 0 132) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat k) ltac:(apply in_seq; lia)). cbv beta zeta in ALL.
  rewrite Z2Nat.id in ALL by lia.
  apply andb_true_iff in ALL as [ALL E6]. apply andb_true_iff in ALL as [ALL E5]. apply andb_true_iff in ALL as [ALL E4].
  apply andb_true_iff in ALL as [ALL E3]. apply andb_true_iff in ALL as [E1 E2].
  apply Nat.eqb_eq in E2. apply Nat.leb_le in E3. apply Nat.eqb_eq in E5. apply Z.eqb_eq in E6.
  split; [| split; [apply notin0_of_forallb; exact E4 | exact E5]].
  rewrite E6, (bytes_eq_chk_s _ _ E2 E1). apply bytes_at_sub; [exact TAB | exact E3].
Qed.

(* [comment removed for export] *)
Lemma strerror_msg_at : forall m e, mem_inv ssegs m ->
  bytes_at ssegs m (strerror_res e) (strerror_msgb e ++ Z_to_bv 8 0 :: strerror_slack e)
  /\ ~ In (Z_to_bv 8 0) (strerror_msgb e) /\ length (strerror_slack e) = 7%nat.
Proof. intros m e MI. apply sr_msg_at; [exact MI | apply strerror_e_range]. Qed.

Lemma strerror_msgb_length : forall e, (length (strerror_msgb e) <= 40)%nat.
Proof.
  intros e. unfold strerror_msgb. pose proof (strerror_e_range e) as R.
  assert (ALL : forallb (fun j : nat => Nat.leb (length (sr_msgb (Z.of_nat j))) 40) (seq 0 132) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat (strerror_e e)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in ALL by lia. apply Nat.leb_le in ALL. exact ALL.
Qed.

Lemma strerror_res_range : forall e, (0x11638 <= strerror_res e /\ strerror_res e + 48 <= 0x11ee8)%Z.
Proof.
  intros e. unfold strerror_res. pose proof (strerror_e_range e) as R.
  assert (ALL : forallb (fun j : nat => (0x11638 <=? sr_res (Z.of_nat j)) && (sr_res (Z.of_nat j) + 48 <=? 0x11ee8))%Z (seq 0 132) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat (strerror_e e)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in ALL by lia. apply andb_true_iff in ALL as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. split; assumption.
Qed.

(* [comment removed for export] *)
Definition strerror_index_eq__stmt : Prop := forall e, (-2^31 <= e < 2^31)%Z ->
  Z.shiftl (Z.land ((0 - Z.b2z (e mod 18446744073709551616 <? 132)%Z) mod 18446744073709551616) (e mod 18446744073709551616)) 1 = (2 * strerror_e e)%Z.
Section Sz11.
Variables e : ltac2:(SecDiet.SzSec.tyM 'strerror_index_eq__stmt "v" @e).
#[using="Type"] Lemma strerror_index_eq__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_index_eq__stmt "v").
Proof.
  intros He.
 unfold strerror_e. rewrite Z.shiftl_mul_pow2 by lia.
  destruct (Z.leb_spec0 0 e).
  - rewrite (Z.mod_small e) by lia. destruct (Z.ltb_spec0 e 132); cbn [Z.b2z andb].
    + change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
    + rewrite Z.mod_0_l, Z.land_0_l by lia. lia.
  - replace (e mod 18446744073709551616)%Z with (18446744073709551616 + e)%Z.
    2:{ symmetry. replace e with ((18446744073709551616 + e) + (-1) * 18446744073709551616)%Z at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    destruct (Z.ltb_spec0 (18446744073709551616 + e) 132); [lia|]. cbn [Z.b2z andb]. rewrite Z.mod_0_l, Z.land_0_l by lia. lia.
Qed.
End Sz11.
Lemma strerror_index_eq : ltac:(let t := eval cbv delta [strerror_index_eq__stmt] in strerror_index_eq__stmt in exact t).
Proof. intros e. ltac2:(SecDiet.SzSec.closeP 'strerror_index_eq__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strerror_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e loc : Z) (catv : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strerror_res e)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom ssegs)
    /\ munch [] m m /\ wmono ssegs m m /\ mem_inv ssegs m
    /\ rw_cells ssegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)]
    /\ rw_cells ssegs m (loc + 40) [C8 catv].

Definition strerror_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e loc : Z) (catv : word),
  rw_cells ssegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->
  rw_cells ssegs m (loc + 40) [C8 catv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z ->
  (48 <= bv_unsigned tp)%Z -> (0 <= loc /\ loc + 48 <= 2^64)%Z ->
  evt ssegs (strerror_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e loc catv m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1e45c) fc None m (seg_rom ssegs)).
Section Sz12.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc catv : ltac2:(SecDiet.SzSec.tyM 'strerror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strerror_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros TLSL LOC MI -> He Htp Hloc.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl ssegs m) as WM.
  pose proof (errmsgidx_at m MI) as TABI.
  set (e' := strerror_e e). pose proof (strerror_e_range e) as He'. fold e' in He'.
  assert (HW : (Z.to_nat (2 * e') + 2 <= length errmsgidx_bytes)%nat).
  { unfold errmsgidx_bytes. rewrite length_map. vm_compute (length errmsgidx_Z). lia. }
  pose proof (bytes_at_read ssegs m ERRMSGIDX errmsgidx_bytes (2 * e') 2 TABI ltac:(lia) HW) as RD. unfold ERRMSGIDX in RD.
  do 8 zstep. rewrite strerror_index_eq by lia. fold e'.
  do 6 zstep. do 3 step.
  replace (71224 + _)%Z with (strerror_res e) by reflexivity.
  unfold strerror_post. finish.
Qed.
End Sz12.
Lemma strerror_spec : ltac:(let t := eval cbv delta [strerror_spec__stmt] in strerror_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc catv. ltac2:(SecDiet.SzSec.closeP 'strerror_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strerror_r_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e : Z) (B n loc : Z) (catv : word) (junk : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (B, B + n)]%Z m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp)
    /\ rw_cells ssegs m' B [CB (length (strerror_msgb e) + 1) (strerror_msgb e ++ [Z_to_bv 8 0]);
                            CB (Z.to_nat n - (length (strerror_msgb e) + 1)) (skipn (length (strerror_msgb e) + 1) junk)]
    /\ rw_cells ssegs m' (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)]
    /\ rw_cells ssegs m' (loc + 40) [C8 catv].

Definition strerror_r_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (n loc : Z) (catv : word) (junk : list byte) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  rw_cells ssegs m (bv_unsigned a1) [CB (Z.to_nat n) junk] ->
  rw_cells ssegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->
  rw_cells ssegs m (loc + 40) [C8 catv] ->
  mem_inv ssegs m ->
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z ->
  a2 = Z_to_bv 64 n -> (41 <= n < 2^63)%Z ->
  (48 <= bv_unsigned tp)%Z -> (0 <= loc /\ loc + 48 <= 2^64)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a1 + n <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z ->           (* [comment removed for export] *)
  (bv_unsigned a1 + n <= bv_unsigned tp - 48 \/ bv_unsigned tp - 40 <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + n <= loc + 40 \/ loc + 48 <= bv_unsigned a1)%Z ->
  (bv_unsigned tp - 40 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned tp - 48)%Z ->
  (loc + 48 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= loc + 40)%Z ->
  (0x11ee8 <= bv_unsigned a1 \/ bv_unsigned a1 + n <= 0x11638)%Z ->      (* [comment removed for export] *)
  evt ssegs (strerror_r_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e (bv_unsigned a1) n loc catv junk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20f74) fc None m (seg_rom ssegs)).
Section Sz13.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e n loc catv junk lo : ltac2:(SecDiet.SzSec.tyM 'strerror_r_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strerror_r_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_r_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST DST TLSL LOC MI -> He -> Hn Htp Hloc LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_cells_CB_length _ _ _ _ _ DST) as JL.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + n)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (strerror_res_range e) as RR. pose proof (strerror_msgb_length e) as ML.
  carve_frame 32%nat ST.
  do 7 step.
  step. call (strerror_spec (Z_to_bv 64 0x20f94) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp); [exact TLSL | exact LOC | exact MI | reflexivity | lia | lia | lia | ].
  clear PC POST.
  lazymatch goal with H : mem_inv ssegs ?mm |- _ => destruct (strerror_msg_at mm e H) as (MSG & NONUL & SL) end.
  rewrite <- (unsigned_lit (strerror_res e)) in MSG by lia.
  step. step. call strlen_spec. 1:{ exact MSG. } 1:{ exact NONUL. } 1:{ rewrite SL, unsigned_lit by lia. Z.div_mod_to_equations; lia. } 1:{ mi. }
  zstep. if_cases K; zify_cond K. { exfalso. lia. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof POST as MSG1.
  replace (strerror_msgb e ++ Z_to_bv 8 0 :: strerror_slack e) with ((strerror_msgb e ++ [Z_to_bv 8 0]) ++ strerror_slack e) in MSG1
    by (rewrite <- app_assoc; reflexivity).
  apply (proj1 (bytes_at_app _ _ _ _ _)) in MSG1. destruct MSG1 as [MSG1 _].
  apply (rw_cells_split_CB ssegs _ _ [] _ _ [] [length (strerror_msgb e) + 1; Z.to_nat n - (length (strerror_msgb e) + 1)]%nat) in DST.
  2:{ cbn [sum_nat]. lia. }
  cbn [mk_CB_cells app] in DST. apply rw_cells_split2 in DST. destruct DST as [DST DST2]. cbn [csize] in DST2.
  step.
  remember (Z_to_bv 64 (Z.of_nat (length (strerror_msgb e)) + 1)) as c2 eqn:Ec2.
  assert (Hc2 : bv_unsigned c2 = (Z.of_nat (length (strerror_msgb e)) + 1)%Z) by (subst c2; apply unsigned_lit; lia).
  call memcpy_spec.
  1:{ exact MSG1. }
  1:{ rewrite length_app. cbn [length]. rewrite Hc2. lia. }
  1:{ rewrite Hc2. replace (Z.to_nat (Z.of_nat (length (strerror_msgb e)) + 1)) with (length (strerror_msgb e) + 1)%nat by lia. exact DST. }
  1:{ rewrite Hc2. rewrite unsigned_lit by lia. lia. }
  1:{ mi. }
  zstep. do 5 step. release_frame FR ST (bv_unsigned sp). step.
  subst c2. rewrite !Hc2 in *. rewrite !(unsigned_lit (strerror_res e)) in * by lia.
  lazymatch goal with H : rw_cells ssegs ?mm (bv_unsigned a1) [CB _ (strerror_msgb e ++ [Z_to_bv 8 0])] |- _ =>
    replace (Z.to_nat (Z.of_nat (length (strerror_msgb e)) + 1)) with (length (strerror_msgb e) + 1)%nat in H by lia;
    pose proof (rw_cells_join2 ssegs mm (bv_unsigned a1) _ _ H DST2) as DSTF end.
  rewrite firstn_all2 in DSTF by (rewrite length_skipn; lia).
  unfold strerror_r_post. finish.
Qed.
End Sz13.
Lemma strerror_r_spec : ltac:(let t := eval cbv delta [strerror_r_spec__stmt] in strerror_r_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e n loc catv junk lo. ltac2:(SecDiet.SzSec.closeP 'strerror_r_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.StrerrorData OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope bv_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv usegs _ |- _ => exact H end.

Definition strerror_entry := 0x1ec1c%Z.
Definition strerror_r_entry := 0x21734%Z.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strerror_e (e : Z) : Z := if ((0 <=? e) && (e <? 132))%Z then e else 0.

(* [comment removed for export] *)
Definition strerror_tab : list byte := errmsgstr_bytes ++ errmsgidx_bytes.

(* [comment removed for export] *)
Definition sr_idx (k : Z) : Z :=
  bv_unsigned (zext 64 (bv_extract 0 16 (le_bytes_to_word (firstn 2 (skipn (Z.to_nat (2 * k)) errmsgidx_bytes))))).
Definition sr_res (k : Z) : Z := ERRMSGSTR + sr_idx k.
Definition sr_msgb (k : Z) : list byte := map (Z_to_bv 8) (nth (Z.to_nat k) strerror_msgZ []).
Definition sr_slack (k : Z) : list byte :=
  firstn 7 (skipn (Z.to_nat (sr_idx k) + length (sr_msgb k) + 1) strerror_tab).

Definition strerror_res (e : Z) : Z := sr_res (strerror_e e).
Definition strerror_msgb (e : Z) : list byte := sr_msgb (strerror_e e).
Definition strerror_slack (e : Z) : list byte := sr_slack (strerror_e e).

Example strerror_res_2 : strerror_res 2 = (0x11638 + 133)%Z. Proof. vm_compute. reflexivity. Qed.
Example strerror_res_neg : strerror_res (-7) = 0x11638%Z. Proof. vm_compute. reflexivity. Qed.
Example strerror_msgb_12 : map bv_unsigned (strerror_msgb 12) = [79; 117; 116; 32; 111; 102; 32; 109; 101; 109; 111; 114; 121]%Z. (* [comment removed for export] *)
Proof. vm_compute. reflexivity. Qed.

Lemma strerror_e_range : forall e, (0 <= strerror_e e < 132)%Z.
Proof. intros e. unfold strerror_e. destruct (Z.leb_spec0 0 e), (Z.ltb_spec0 e 132); cbn; lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma errmsgidx_at : forall m, mem_inv usegs m -> bytes_at usegs m ERRMSGIDX errmsgidx_bytes.
Proof.
  intros m MI.
  pose proof (ro_cells_image usegs m ERRMSGIDX errmsgidx_bytes MI ltac:(vm_compute; reflexivity) ltac:(unfold ERRMSGIDX; lia)
                ltac:(unfold errmsgidx_bytes, ERRMSGIDX; rewrite length_map; vm_compute (length errmsgidx_Z); lia)) as RO.
  apply ro_cells_bytes_at in RO. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma strerror_tab_at : forall m, mem_inv usegs m -> bytes_at usegs m ERRMSGSTR strerror_tab.
Proof.
  intros m MI.
  pose proof (ro_cells_image usegs m ERRMSGSTR strerror_tab MI ltac:(vm_compute; reflexivity) ltac:(unfold ERRMSGSTR; lia)
                ltac:(unfold strerror_tab, errmsgstr_bytes, errmsgidx_bytes, ERRMSGSTR; rewrite length_app, !length_map;
                      vm_compute (length errmsgidx_Z); vm_compute (length errmsgstr_Z); lia)) as RO.
  apply ro_cells_bytes_at in RO. cbn [cells_bytes cbytes] in RO. rewrite app_nil_r in RO. exact RO.
Qed.

Lemma bytes_at_sub : forall m A l (i n : nat), bytes_at usegs m A l -> (i + n <= length l)%nat ->
  bytes_at usegs m (A + Z.of_nat i) (firstn n (skipn i l)).
Proof.
  intros m A l i n H Hl.
  rewrite <- (firstn_skipn i l) in H. apply (proj1 (bytes_at_app _ _ _ _ _)) in H. destruct H as [_ H].
  rewrite length_firstn, Nat.min_l in H by lia.
  rewrite <- (firstn_skipn n (skipn i l)) in H. apply (proj1 (bytes_at_app _ _ _ _ _)) in H. destruct H as [H _]. exact H.
Qed.

Lemma notin0_of_forallb : forall l : list byte,
  forallb (fun b => negb (bv_unsigned b =? 0)%Z) l = true -> ~ In (Z_to_bv 8 0) l.
Proof.
  intros l H Hin. apply forallb_forall with (x := Z_to_bv 8 0) in H; [|exact Hin]. cbn in H. discriminate.
Qed.

Lemma Zcases_nat : forall (P : Z -> Prop) (n : nat),
  (forall k : nat, (k < n)%nat -> P (Z.of_nat k)) -> forall z, (0 <= z < Z.of_nat n)%Z -> P z.
Proof. intros P n H z Hz. replace z with (Z.of_nat (Z.to_nat z)) by lia. apply H. lia. Qed.

Local Ltac sr_case TAB :=
  lazymatch goal with |- bytes_at _ _ (sr_res (Z.of_nat ?k)) _ /\ _ =>
    let i := eval vm_compute in (Z.to_nat (sr_idx (Z.of_nat k))) in
    let n := eval vm_compute in (length (sr_msgb (Z.of_nat k)) + 8)%nat in
    split; [ replace (sr_res (Z.of_nat k)) with (ERRMSGSTR + Z.of_nat i)%Z by (vm_compute; reflexivity);
             replace (sr_msgb (Z.of_nat k) ++ Z_to_bv 8 0 :: sr_slack (Z.of_nat k)) with (firstn n (skipn i strerror_tab)) by (vm_compute; reflexivity);
             apply (bytes_at_sub _ _ _ i n TAB); vm_compute; lia
           | split; [ apply notin0_of_forallb; vm_compute; reflexivity | vm_compute; reflexivity ] ]
  end.

(* [comment removed for export] *)
Lemma bytes_eq_chk_s : forall l1 l2 : list byte, length l1 = length l2 ->
  forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p))) (combine l1 l2) = true -> l1 = l2.
Proof.
  induction l1 as [|a l1 IH]; intros [|b l2] Hl H; cbn in *; try discriminate; [reflexivity|].
  apply andb_true_iff in H as [H1 H2]. apply Z.eqb_eq in H1. f_equal; [apply bv_eq; exact H1 | apply IH; [lia | exact H2]].
Qed.

Lemma sr_msg_at : forall m k, mem_inv usegs m -> (0 <= k < 132)%Z ->
  bytes_at usegs m (sr_res k) (sr_msgb k ++ Z_to_bv 8 0 :: sr_slack k) /\ ~ In (Z_to_bv 8 0) (sr_msgb k) /\ length (sr_slack k) = 7%nat.
Proof.
  intros m k MI Hk. pose proof (strerror_tab_at m MI) as TAB.
  assert (ALL : forallb (fun j : nat =>
      let K := Z.of_nat j in let i := Z.to_nat (sr_idx K) in let n := (length (sr_msgb K) + 8)%nat in
      forallb (fun p => Z.eqb (bv_unsigned (fst p)) (bv_unsigned (snd p)))
              (combine (sr_msgb K ++ Z_to_bv 8 0 :: sr_slack K) (firstn n (skipn i strerror_tab)))
      && Nat.eqb (length (sr_msgb K ++ Z_to_bv 8 0 :: sr_slack K)) (length (firstn n (skipn i strerror_tab)))
      && Nat.leb (i + n) (length strerror_tab)
      && forallb (fun b => negb (bv_unsigned b =? 0)%Z) (sr_msgb K)
      && Nat.eqb (length (sr_slack K)) 7
      && Z.eqb (sr_res K) (ERRMSGSTR + Z.of_nat i)) (seq 0 132) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat k) ltac:(apply in_seq; lia)). cbv beta zeta in ALL.
  rewrite Z2Nat.id in ALL by lia.
  apply andb_true_iff in ALL as [ALL E6]. apply andb_true_iff in ALL as [ALL E5]. apply andb_true_iff in ALL as [ALL E4].
  apply andb_true_iff in ALL as [ALL E3]. apply andb_true_iff in ALL as [E1 E2].
  apply Nat.eqb_eq in E2. apply Nat.leb_le in E3. apply Nat.eqb_eq in E5. apply Z.eqb_eq in E6.
  split; [| split; [apply notin0_of_forallb; exact E4 | exact E5]].
  rewrite E6, (bytes_eq_chk_s _ _ E2 E1). apply bytes_at_sub; [exact TAB | exact E3].
Qed.

(* [comment removed for export] *)
Lemma strerror_msg_at : forall m e, mem_inv usegs m ->
  bytes_at usegs m (strerror_res e) (strerror_msgb e ++ Z_to_bv 8 0 :: strerror_slack e)
  /\ ~ In (Z_to_bv 8 0) (strerror_msgb e) /\ length (strerror_slack e) = 7%nat.
Proof. intros m e MI. apply sr_msg_at; [exact MI | apply strerror_e_range]. Qed.

Lemma strerror_msgb_length : forall e, (length (strerror_msgb e) <= 40)%nat.
Proof.
  intros e. unfold strerror_msgb. pose proof (strerror_e_range e) as R.
  assert (ALL : forallb (fun j : nat => Nat.leb (length (sr_msgb (Z.of_nat j))) 40) (seq 0 132) = true) by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat (strerror_e e)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in ALL by lia. apply Nat.leb_le in ALL. exact ALL.
Qed.

Lemma strerror_res_range : forall e, (0x11638 <= strerror_res e /\ strerror_res e + 48 <= 0x11ee8)%Z.
Proof.
  intros e. unfold strerror_res. pose proof (strerror_e_range e) as R.
  assert (ALL : forallb (fun j : nat => (0x11638 <=? sr_res (Z.of_nat j)) && (sr_res (Z.of_nat j) + 48 <=? 0x11ee8))%Z (seq 0 132) = true)
    by (vm_compute; reflexivity).
  rewrite forallb_forall in ALL. specialize (ALL (Z.to_nat (strerror_e e)) ltac:(apply in_seq; lia)).
  rewrite Z2Nat.id in ALL by lia. apply andb_true_iff in ALL as [A1 A2]. apply Z.leb_le in A1. apply Z.leb_le in A2. split; assumption.
Qed.

(* [comment removed for export] *)
Definition strerror_index_eq__stmt : Prop := forall e, (-2^31 <= e < 2^31)%Z ->
  Z.shiftl (Z.land ((0 - Z.b2z (e mod 18446744073709551616 <? 132)%Z) mod 18446744073709551616) (e mod 18446744073709551616)) 1 = (2 * strerror_e e)%Z.
Section Sz11.
Variables e : ltac2:(SecDiet.SzSec.tyM 'strerror_index_eq__stmt "v" @e).
#[using="Type"] Lemma strerror_index_eq__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_index_eq__stmt "v").
Proof.
  intros He.
 unfold strerror_e. rewrite Z.shiftl_mul_pow2 by lia.
  destruct (Z.leb_spec0 0 e).
  - rewrite (Z.mod_small e) by lia. destruct (Z.ltb_spec0 e 132); cbn [Z.b2z andb].
    + change ((0 - 1) mod 18446744073709551616)%Z with (Z.ones 64). rewrite Z.land_comm, Z.land_ones by lia. rewrite Z.mod_small by lia. lia.
    + rewrite Z.mod_0_l, Z.land_0_l by lia. lia.
  - replace (e mod 18446744073709551616)%Z with (18446744073709551616 + e)%Z.
    2:{ symmetry. replace e with ((18446744073709551616 + e) + (-1) * 18446744073709551616)%Z at 1 by lia. rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    destruct (Z.ltb_spec0 (18446744073709551616 + e) 132); [lia|]. cbn [Z.b2z andb]. rewrite Z.mod_0_l, Z.land_0_l by lia. lia.
Qed.
End Sz11.
Lemma strerror_index_eq : ltac:(let t := eval cbv delta [strerror_index_eq__stmt] in strerror_index_eq__stmt in exact t).
Proof. intros e. ltac2:(SecDiet.SzSec.closeP 'strerror_index_eq__body "v"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition strerror_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e loc : Z) (catv : word) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strerror_res e)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom usegs)
    /\ munch [] m m /\ wmono usegs m m /\ mem_inv usegs m
    /\ rw_cells usegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)]
    /\ rw_cells usegs m (loc + 40) [C8 catv].

Definition strerror_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e loc : Z) (catv : word),
  rw_cells usegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->
  rw_cells usegs m (loc + 40) [C8 catv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z ->
  (48 <= bv_unsigned tp)%Z -> (0 <= loc /\ loc + 48 <= 2^64)%Z ->
  evt usegs (strerror_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e loc catv m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1ec1c) fc None m (seg_rom usegs)).
Section Sz12.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc catv : ltac2:(SecDiet.SzSec.tyM 'strerror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strerror_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros TLSL LOC MI -> He Htp Hloc.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (errmsgidx_at m MI) as TABI.
  set (e' := strerror_e e). pose proof (strerror_e_range e) as He'. fold e' in He'.
  assert (HW : (Z.to_nat (2 * e') + 2 <= length errmsgidx_bytes)%nat).
  { unfold errmsgidx_bytes. rewrite length_map. vm_compute (length errmsgidx_Z). lia. }
  pose proof (bytes_at_read usegs m ERRMSGIDX errmsgidx_bytes (2 * e') 2 TABI ltac:(lia) HW) as RD. unfold ERRMSGIDX in RD.
  do 8 zstep. rewrite strerror_index_eq by lia. fold e'.
  do 6 zstep. do 3 step.
  replace (71224 + _)%Z with (strerror_res e) by reflexivity.
  unfold strerror_post. finish.
Qed.
End Sz12.
Lemma strerror_spec : ltac:(let t := eval cbv delta [strerror_spec__stmt] in strerror_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e loc catv. ltac2:(SecDiet.SzSec.closeP 'strerror_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition strerror_r_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (e : Z) (B n loc : Z) (catv : word) (junk : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp); (B, B + n)]%Z m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ rw_cells usegs m' B [CB (length (strerror_msgb e) + 1) (strerror_msgb e ++ [Z_to_bv 8 0]);
                            CB (Z.to_nat n - (length (strerror_msgb e) + 1)) (skipn (length (strerror_msgb e) + 1) junk)]
    /\ rw_cells usegs m' (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)]
    /\ rw_cells usegs m' (loc + 40) [C8 catv].

Definition strerror_r_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (e : Z) (n loc : Z) (catv : word) (junk : list byte) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  rw_cells usegs m (bv_unsigned a1) [CB (Z.to_nat n) junk] ->
  rw_cells usegs m (bv_unsigned tp + -48) [C8 (Z_to_bv 64 loc)] ->
  rw_cells usegs m (loc + 40) [C8 catv] ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 e -> (-2^31 <= e < 2^31)%Z ->
  a2 = Z_to_bv 64 n -> (41 <= n < 2^63)%Z ->
  (48 <= bv_unsigned tp)%Z -> (0 <= loc /\ loc + 48 <= 2^64)%Z ->
  (lo <= bv_unsigned sp - 32)%Z ->
  (bv_unsigned a1 + n <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z ->           (* [comment removed for export] *)
  (bv_unsigned a1 + n <= bv_unsigned tp - 48 \/ bv_unsigned tp - 40 <= bv_unsigned a1)%Z ->
  (bv_unsigned a1 + n <= loc + 40 \/ loc + 48 <= bv_unsigned a1)%Z ->
  (bv_unsigned tp - 40 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= bv_unsigned tp - 48)%Z ->
  (loc + 48 <= bv_unsigned sp - 32 \/ bv_unsigned sp <= loc + 40)%Z ->
  (0x11ee8 <= bv_unsigned a1 \/ bv_unsigned a1 + n <= 0x11638)%Z ->      (* [comment removed for export] *)
  evt usegs (strerror_r_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc e (bv_unsigned a1) n loc catv junk lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x21734) fc None m (seg_rom usegs)).
Section Sz13.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e n loc catv junk lo : ltac2:(SecDiet.SzSec.tyM 'strerror_r_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma strerror_r_spec__body : ltac2:(SecDiet.SzSec.bodyP 'strerror_r_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST DST TLSL LOC MI -> He -> Hn Htp Hloc LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6.
  pose proof (rw_cells_bound _ _ _ _ DST) as DB. cbn [cells_size csize Nat.add] in DB.
  pose proof (rw_cells_CB_length _ _ _ _ _ DST) as JL.
  pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp); (bv_unsigned a1, bv_unsigned a1 + n)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (proj1 ST) as LO0. cbn beta in LO0. pose proof (bv_unsigned_in_range 64 sp) as Rsp. unfold bv_modulus in Rsp. cbn in Rsp.
  pose proof (strerror_res_range e) as RR. pose proof (strerror_msgb_length e) as ML.
  carve_frame 32%nat ST.
  do 7 step.
  step. call (strerror_spec (Z_to_bv 64 0x21754) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp); [exact TLSL | exact LOC | exact MI | reflexivity | lia | lia | lia | ].
  clear PC POST.
  lazymatch goal with H : mem_inv usegs ?mm |- _ => destruct (strerror_msg_at mm e H) as (MSG & NONUL & SL) end.
  rewrite <- (unsigned_lit (strerror_res e)) in MSG by lia.
  step. step. call strlen_spec. 1:{ exact MSG. } 1:{ exact NONUL. } 1:{ rewrite SL, unsigned_lit by lia. Z.div_mod_to_equations; lia. } 1:{ mi. }
  zstep. if_cases K; zify_cond K. { exfalso. lia. }
  zstep. zstep. zstep.
  (* [comment removed for export] *)
  pose proof POST as MSG1.
  replace (strerror_msgb e ++ Z_to_bv 8 0 :: strerror_slack e) with ((strerror_msgb e ++ [Z_to_bv 8 0]) ++ strerror_slack e) in MSG1
    by (rewrite <- app_assoc; reflexivity).
  apply (proj1 (bytes_at_app _ _ _ _ _)) in MSG1. destruct MSG1 as [MSG1 _].
  apply (rw_cells_split_CB usegs _ _ [] _ _ [] [length (strerror_msgb e) + 1; Z.to_nat n - (length (strerror_msgb e) + 1)]%nat) in DST.
  2:{ cbn [sum_nat]. lia. }
  cbn [mk_CB_cells app] in DST. apply rw_cells_split2 in DST. destruct DST as [DST DST2]. cbn [csize] in DST2.
  step.
  remember (Z_to_bv 64 (Z.of_nat (length (strerror_msgb e)) + 1)) as c2 eqn:Ec2.
  assert (Hc2 : bv_unsigned c2 = (Z.of_nat (length (strerror_msgb e)) + 1)%Z) by (subst c2; apply unsigned_lit; lia).
  call memcpy_spec.
  1:{ exact MSG1. }
  1:{ rewrite length_app. cbn [length]. rewrite Hc2. lia. }
  1:{ rewrite Hc2. replace (Z.to_nat (Z.of_nat (length (strerror_msgb e)) + 1)) with (length (strerror_msgb e) + 1)%nat by lia. exact DST. }
  1:{ rewrite Hc2. rewrite unsigned_lit by lia. lia. }
  1:{ mi. }
  zstep. do 5 step. release_frame FR ST (bv_unsigned sp). step.
  subst c2. rewrite !Hc2 in *. rewrite !(unsigned_lit (strerror_res e)) in * by lia.
  lazymatch goal with H : rw_cells usegs ?mm (bv_unsigned a1) [CB _ (strerror_msgb e ++ [Z_to_bv 8 0])] |- _ =>
    replace (Z.to_nat (Z.of_nat (length (strerror_msgb e)) + 1)) with (length (strerror_msgb e) + 1)%nat in H by lia;
    pose proof (rw_cells_join2 usegs mm (bv_unsigned a1) _ _ H DST2) as DSTF end.
  rewrite firstn_all2 in DSTF by (rewrite length_skipn; lia).
  unfold strerror_r_post. finish.
Qed.
End Sz13.
Lemma strerror_r_spec : ltac:(let t := eval cbv delta [strerror_r_spec__stmt] in strerror_r_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m e n loc catv junk lo. ltac2:(SecDiet.SzSec.closeP 'strerror_r_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End TwB.
End F_strerror.

(* [comment removed for export] *)
Module F_stdio_write.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_WRITE : Z := 0x1b3f4.
Definition STDIO_WRITE_DEPTH : Z := 112.
Definition SW_SHORT : Z := 0x1b514.   (* [comment removed for export] *)
Definition SW_OK : Z := 0x1b488.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition wdec_Some__stmt : Prop := forall f rem rsp cnt,
  wdec f rem rsp = Some cnt ->
  rsp = eff0 (Z_to_bv 64 cnt) /\ 0 <= cnt <= rem /\ 0 <= cnt < 2^64 /\ (cnt = rem \/ 1 <= cnt < rem).
Section Sz1.
Variables f rem rsp cnt : ltac2:(SecDiet.SzSec.tyM 'wdec_Some__stmt "vvvv" @f).
#[using="Type"] Lemma wdec_Some__body : ltac2:(SecDiet.SzSec.bodyP 'wdec_Some__stmt "vvvv").
Proof.
  intros H.
 unfold wdec in H. destruct (f_chan f).
  - apply dec_writev_Some in H as (Hr & -> & Hc). split; [reflexivity|]. lia.
  - unfold dec_writevf_ok, dec_writevf in H.
    destruct (dec_plain (fun v => v =? rem) rsp) as [[e|v]|] eqn:E; try discriminate H.
    injection H as <-. apply dec_plain_Some in E as (-> & Hok & Hv).
    apply Z.eqb_eq in Hok. subst v. split; [reflexivity|]. lia.
Qed.
End Sz1.
Lemma wdec_Some : ltac:(let t := eval cbv delta [wdec_Some__stmt] in wdec_Some__stmt in exact t).
Proof. intros f rem rsp cnt. ltac2:(SecDiet.SzSec.closeP 'wdec_Some__body "vvvv"). Qed.

(* [comment removed for export] *)
Definition at_wnode__stmt : Prop := forall f L (R F : bvmap 5 word) pc fc m (A : Z) (iovs : list (word * word)),
  (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^32 /\ 1 <= Z.of_nat (length (concat (map to_bytes L))))) ->
  reg_get R 10 = Z_to_bv 64 (f_fd f) ->
  reg_get R 11 = Z_to_bv 64 A -> 0 <= A < 2^64 ->
  reg_get R 12 = Z_to_bv 64 (Z.of_nat (length L)) ->
  (1 <= length L <= 2)%nat ->
  A + 16 * Z.of_nat (length L) <= 2^47 ->   (* [comment removed for export] *)
  Z.of_nat (length (concat (map to_bytes L))) <= max_write ->
  bytes_at ssegs m A (iovec_bytes iovs) ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47   (* [comment removed for export] *)
                         /\ bytes_at ssegs m (bv_unsigned (fst iov)) bs) iovs (map to_bytes L) ->
  at_node ssegs (wnode f L) (MSsvc R F pc (Z_to_bv 64 66) fc None m (seg_rom ssegs)).
Section Sz2.
Variables f L R F pc fc m A iovs : ltac2:(SecDiet.SzSec.tyM 'at_wnode__stmt "vvvvvvvvv" @f).
#[using="Type"] Lemma at_wnode__body : ltac2:(SecDiet.SzSec.bodyP 'at_wnode__stmt "vvvvvvvvv").
Proof.
  intros CH R10 R11 HA R12 HL HA47 HT HIOV HF.
  unfold wnode. destruct (f_chan f).
  - cbn [at_node]. unfold areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS].
    rewrite R10, R11, R12, length_map. rewrite unsigned_lit by lia.
    repeat split; try reflexivity; try lia. exists iovs. split; assumption.
  - destruct CH as [FD TOT]. cbn [at_node]. unfold areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS].
    rewrite R10, R11, R12, length_map. rewrite unsigned_lit by lia.
    repeat split; try reflexivity; try lia. exists iovs. split; assumption.
Qed.
End Sz2.
Lemma at_wnode : ltac:(let t := eval cbv delta [at_wnode__stmt] in at_wnode__stmt in exact t).
Proof. intros f L R F pc fc m A iovs. ltac2:(SecDiet.SzSec.closeP 'at_wnode__body "vvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition iov_bytes2__stmt : Prop := forall m A j8 (w0 w1 w2 w3 : word) rest,
  rw_cells ssegs m A (CB 8 j8 :: C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: rest) ->
  bytes_at ssegs m (A + 8) (iovec_bytes [(w0, w1); (w2, w3)]) /\ bytes_at ssegs m (A + 24) (iovec_bytes [(w2, w3)]).
Section Sz3.
Variables m A j8 w0 w1 w2 w3 rest : ltac2:(SecDiet.SzSec.tyM 'iov_bytes2__stmt "vvvvvvvv" @m).
#[using="Type"] Lemma iov_bytes2__body : ltac2:(SecDiet.SzSec.bodyP 'iov_bytes2__stmt "vvvvvvvv").
Proof.
  intros FR.
  destruct FR as [[WF FB] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [L8 _].
  cbn [cells_bytes cbytes] in FB.
  apply bytes_at_app in FB as [_ FB]. rewrite L8 in FB.
  apply bytes_at_app in FB as [FB0 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB3 _].
  cbn [iovec_bytes flat_map fst snd]. rewrite !app_nil_r. split.
  - apply bytes_at_app. rewrite length_app, !length_le8. split.
    + apply bytes_at_app. rewrite length_le8. split.
      * replace (A + 8) with (A + Z.of_nat 8) by lia. exact FB0.
      * replace (A + 8 + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB1.
    + apply bytes_at_app. rewrite length_le8. split.
      * replace (A + 8 + Z.of_nat (8 + 8)) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
      * replace (A + 8 + Z.of_nat (8 + 8) + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
  - apply bytes_at_app. rewrite length_le8. split.
    + replace (A + 24) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
    + replace (A + 24 + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
Qed.
End Sz3.
Lemma iov_bytes2 : ltac:(let t := eval cbv delta [iov_bytes2__stmt] in iov_bytes2__stmt in exact t).
Proof. intros m A j8 w0 w1 w2 w3 rest. ltac2:(SecDiet.SzSec.closeP 'iov_bytes2__body "vvvvvvvv"). Qed.

Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.

Lemma bytes_at_skipn : forall m A bs n, bytes_at ssegs m A bs -> (n <= length bs)%nat ->
  bytes_at ssegs m (A + Z.of_nat n) (skipn n bs).
Proof.
  intros m A bs n H Hn. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H as [_ H].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

Section StdioWrite.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition fcells (flags : word) (rpos rend closefn : Z) (wend wpos wbase : Z)
      (readfn writefn seekfn B bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
    file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next fd mode lbf tail.

  Definition sw_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)].

  (* [comment removed for export] *)
  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn readfn writefn seekfn B bufsize prev next : Z) (mode : word) (lbf : Z) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => f' = set_w true [] f /\ st' = st /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch (sw_W sp Fp) m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' Fp (fcells flags rpos rend closefn (B + bufsize) B B readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail)
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition sw_ok_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z) (mode : word) (lbf : Z) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word) (j8 : list byte) (w0 w1 w2 w3 : word) (m' : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp) a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 (Z_to_bv 64 ssp_guard) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 SW_OK) fc None m' (seg_rom ssegs)
      /\ munch (sw_W sp Fp) m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp + -112)
      /\ rw_cells ssegs m' (bv_unsigned sp + -112)
           [CB 8 j8; C8 w0; C8 w1; C8 w2; C8 w3; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells ssegs m' Fp (fcells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail)
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition sw_tail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st st' : St) (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z)
      (mode : word) (lbf : Z) (tail : list byte) (len lo : Z) (canary : word) (m : mem) ms u,
    sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m u st' ms ->
    (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (lo <= bv_unsigned sp - 112) ->
    (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
    (0 <= B) -> (0 <= bufsize) -> (B + bufsize < 2^64) -> (0 <= len < 2^64) ->
    evt ssegs (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m (set_w true [] f) st') ms.
  Section Sz7.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st st' Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m ms u : ltac2:(SecDiet.SzSec.tyM 'sw_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma sw_tail__body : ltac2:(SecDiet.SzSec.bodyP 'sw_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros POST Fp0 FPLO LO FSEP1 FSEP2 B0 BS0 BShi LEN.
    destruct POST as [-> POST]. destruct_exs POST.
    destruct POST as (-> & MU & WM & MI & ST & FR & FC & [GOT GUARD]).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold fcells, file_cells in FC. unfold got_ssp, ssp_guard, SW_OK in *.
    rename x23 into m1. unfold sw_W, STDIO_WRITE_DEPTH in MU.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size csize Nat.add] in FB.
    do 7 step.
    (* [comment removed for export] *)
    step. step. step. if_false.
    do 10 step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold stdio_write_post, fcells, file_cells. split; [reflexivity|]. split; [reflexivity|].
    sys_finish. split; [exact GOT | exact GUARD].
  Qed.
  End Sz7.
  Lemma sw_tail : ltac:(let t := eval cbv delta [sw_tail__stmt] in sw_tail__stmt in exact t).
  Proof using Type. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st st' Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m ms u. ltac2:(SecDiet.SzSec.closeP 'sw_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Section Loop.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z)
              (mode : word) (lbf : Z) (tail : list byte) (s : list Z) (S lo : Z) (canary : word) (m : mem).
    #[local] Notation len := (zlength s) (only parsing).
    #[local] Notation wb := (f_wbuf f) (only parsing).
    #[local] Notation FCELLS := (fcells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail) (only parsing).
    #[local] Notation QOK := (sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend wpos wbase
                 readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m) (only parsing).

    Hypothesis CH : if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31).
    Hypothesis LO : lo <= bv_unsigned sp - 112.
    Hypothesis SP47 : bv_unsigned sp <= 2^47.   (* [comment removed for export] *)
    Hypothesis GLO : 0x55000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo \/ bv_unsigned sp <= Fp.
    Hypothesis S0 : 0 <= S < 2^64.
    Hypothesis Shi : S + len <= 2^47.   (* [comment removed for export] *)
    Hypothesis LENW : zlength wb + len <= 2^26.
    Hypothesis SEPS : s = [] \/ ((S + len <= lo \/ bv_unsigned sp <= S) /\ (S + len <= Fp + 32 \/ Fp + 64 <= S)).
    Hypothesis SRC : bytes_at ssegs m S (to_bytes s).      (* [comment removed for export] *)
    Hypothesis B0 : 0 <= B.
    Hypothesis BWB : B + zlength wb <= 2^47.   (* [comment removed for export] *)
    Hypothesis SEPB : (B + zlength wb <= lo \/ bv_unsigned sp <= B) /\ (B + zlength wb <= Fp + 32 \/ Fp + 64 <= B).
    Hypothesis BUFB : bytes_at ssegs m B (to_bytes wb).    (* [comment removed for export] *)

    Definition src_at__stmt : Prop := forall m1 k, munch (sw_W sp Fp) m m1 -> 0 <= k <= len ->
      bytes_at ssegs m1 (S + k) (to_bytes (skipn (Z.to_nat k) s)).
    Section Sz8.
    Variables m1 k : ltac2:(SecDiet.SzSec.tyM 'src_at__stmt "vv" @m1).
    Lemma src_at__body : ltac2:(SecDiet.SzSec.bodyP 'src_at__stmt "vv").
    Proof using FPLO LENW LO S0 SEPB SEPS SRC Shi. pin_using (fun (FPLO LENW LO S0 SEPB SEPS SRC Shi : unit) => tt).
      intros MU Hk.
 rewrite to_bytes_skipn.
      replace (S + k) with (S + Z.of_nat (Z.to_nat k)) by lia.
      apply bytes_at_skipn; [| rewrite length_to_bytes; unfold zlength in Hk; lia].
      destruct SEPS as [-> | [SEP1 SEP2]].
      - apply bytes_at_nil. lia.
      - apply (bytes_at_transport _ _ _ m1 _ _ SRC MU). unfold sw_W, STDIO_WRITE_DEPTH. cbn [disjoint_from].
        rewrite length_to_bytes. unfold zlength in *. lia.
    Qed.
    End Sz8.
    Lemma src_at : ltac:(let t := eval cbv delta [src_at__stmt] in src_at__stmt in exact t).
    Proof using FPLO LENW LO S0 SEPB SEPS SRC Shi. intros m1 k. ltac2:(SecDiet.SzSec.closeP 'src_at__body "vv"). Qed.

    Definition buf_at__stmt : Prop := forall m1 k, munch (sw_W sp Fp) m m1 -> 0 <= k <= zlength wb ->
      bytes_at ssegs m1 (B + k) (to_bytes (skipn (Z.to_nat k) wb)).
    Section Sz9.
    Variables m1 k : ltac2:(SecDiet.SzSec.tyM 'buf_at__stmt "vv" @m1).
    Lemma buf_at__body : ltac2:(SecDiet.SzSec.bodyP 'buf_at__stmt "vv").
    Proof using B0 BUFB BWB FPLO LENW LO SEPB SP47. pin_using (fun (B0 BUFB BWB FPLO LENW LO SEPB SP47 : unit) => tt).
      intros MU Hk.
 rewrite to_bytes_skipn.
      replace (B + k) with (B + Z.of_nat (Z.to_nat k)) by lia.
      apply bytes_at_skipn; [| rewrite length_to_bytes; unfold zlength in Hk; lia].
      destruct (f_wbuf f) as [|b0 wb'] eqn:EWB.
      - apply bytes_at_nil. lia.
      - destruct SEPB as [SEP1 SEP2].
        apply (bytes_at_transport _ _ _ m1 _ _ BUFB MU). unfold sw_W, STDIO_WRITE_DEPTH. cbn [disjoint_from].
        rewrite length_to_bytes. unfold zlength in *. cbn [length] in *. lia.
    Qed.
    End Sz9.
    Lemma buf_at : ltac:(let t := eval cbv delta [buf_at__stmt] in buf_at__stmt in exact t).
    Proof using B0 BUFB BWB FPLO LENW LO SEPB SP47. intros m1 k. ltac2:(SecDiet.SzSec.closeP 'buf_at__body "vv"). Qed.

    (* [comment removed for export] *)
    Lemma sw_loopB : forall fuel (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (j8 : list byte) (w0 w1 : word)
        (k cnt : Z) (m1 : mem),
      rw_cells ssegs m1 (bv_unsigned sp + -112)
        [CB 8 j8; C8 w0; C8 w1; C8 (Z_to_bv 64 (S + k)); C8 (Z_to_bv 64 (len - k)); C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m1 Fp FCELLS ->
      ssp_cells m1 canary -> stk ssegs m1 lo (bv_unsigned sp + -112) -> mem_inv ssegs m1 ->
      munch (sw_W sp Fp) m m1 -> wmono ssegs m m1 ->
      0 <= k -> 1 <= cnt -> k + cnt < len ->
      implM ssegs (writev_loop fuel f [skipn (Z.to_nat (k + cnt)) s] (len - k - cnt)) st QOK
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 cnt) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -88)) x20 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 (len - k))
                 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SW_SHORT) fc None m1 (seg_rom ssegs)).
    Proof using CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi. pin_using (fun (CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi : unit) => tt).
      induction fuel as [|fuel IH]; intros until m1; intros FR FC SSP ST MI MU WM K0 C1 KC.
      { cbn [writev_loop]. apply implM_unr. }
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, SW_SHORT in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold sw_W, STDIO_WRITE_DEPTH in MU.
      cbn [writev_loop]. apply implM_sys_bind.
      unfold zlength in *.
      assert (LS : Z.of_nat (length (to_bytes s)) = Z.of_nat (length s)) by (rewrite length_to_bytes; reflexivity).
      step. if_cases Hc; zify_cond Hc. 1:{ exfalso. clear IH. lia. }
      zs. zs.
      replace (Z.of_nat (length s) - k <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      assert (FD : 0 <= f_fd f < 2^31) by (clear IH; destruct (f_chan f); lia).
      zs. zs.
      zs. zs. zs. rewrite Z.land_0_l. zs. rewrite Z.sub_0_r. zs. zs.
      zs. if_cases Hb; zify_cond Hb. 2:{ exfalso. clear IH. lia. }
      zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
      zs. zs. zs. zs. zs.
      step_ecall. split.
      { (* [comment removed for export] *)
        lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells ssegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
        eapply at_wnode with (A := bv_unsigned sp + -88)
          (iovs := [(Z_to_bv 64 (S + k + cnt), Z_to_bv 64 (Z.of_nat (length s) - k - cnt))]).
        - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn. lia.
        - reflexivity.
        - reflexivity.
        - clear IH; lia.
        - reflexivity.
        - cbn; lia.
        - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
        - clear IH. cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn.
          replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
        - constructor; [|constructor]. split; [|split].
          + cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. clear IH; lia.
          + cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes, length_skipn. clear IH; lia.   (* [comment removed for export] *)
          + cbn [fst]. rewrite unsigned_lit by (clear IH; lia).
            replace (S + k + cnt) with (S + (k + cnt)) by lia. apply src_at; [exact MU | clear IH; unfold zlength; lia]. }
      (* [comment removed for export] *)
      intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implM_prefix. sys_nret.
      (* [comment removed for export] *)
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x1b50c)) with (Z_to_bv 64 0x1b50c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zs. zs.
      destruct Hcases as [-> | Hshort].
      - (* [comment removed for export] *)
        rewrite Z.eqb_refl. if_true.
        apply evt_done. apply implM_ret. apply evt_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      - (* [comment removed for export] *)
        replace (cnt' =? Z.of_nat (length s) - k - cnt) with false by (symmetry; apply Z.eqb_neq; lia).
        if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
        cbn [advance_iovs].
        replace (zlength (skipn (Z.to_nat (k + cnt)) s) <? cnt') with false.
        2:{ symmetry. apply Z.ltb_ge. unfold zlength. rewrite length_skipn. clear IH. lia. }
        rewrite skipn_skipn.
        replace (Z.to_nat cnt' + Z.to_nat (k + cnt))%nat with (Z.to_nat ((k + cnt) + cnt')) by lia.
        replace (Z.of_nat (length s) - k - cnt - cnt') with (Z.of_nat (length s) - (k + cnt) - cnt') by lia.
        replace (Z.of_nat (length s) - k - cnt) with (Z.of_nat (length s) - (k + cnt)) in * by lia.
        replace (S + k + cnt) with (S + (k + cnt)) in * by lia.
        apply evt_done. eapply IH; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | lia | lia | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma sw_loopA : forall fuel (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (j8 : list byte)
        (k cnt : Z) (m1 : mem),
      rw_cells ssegs m1 (bv_unsigned sp + -112)
        [CB 8 j8; C8 (Z_to_bv 64 (B + k)); C8 (Z_to_bv 64 (zlength wb - k)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 len); C8 canary;
         C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m1 Fp FCELLS ->
      ssp_cells m1 canary -> stk ssegs m1 lo (bv_unsigned sp + -112) -> mem_inv ssegs m1 ->
      munch (sw_W sp Fp) m m1 -> wmono ssegs m m1 ->
      0 <= k <= zlength wb -> 1 <= cnt -> k + cnt < zlength wb + len ->
      implM ssegs (writev_loop fuel f (advance_iovs [skipn (Z.to_nat k) wb; s] cnt) (zlength wb - k + len - cnt)) st QOK
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 cnt) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -104)) x20 (Z_to_bv 64 ssp_guard)
                 (Z_to_bv 64 (zlength wb - k + len)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SW_SHORT) fc None m1 (seg_rom ssegs)).
    Proof using B0 BUFB BWB CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi. pin_using (fun (B0 BUFB BWB CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi : unit) => tt).
      induction fuel as [|fuel IH]; intros until m1; intros FR FC SSP ST MI MU WM K0 C1 KC.
      { cbn [writev_loop]. destruct (zlength (skipn (Z.to_nat k) wb) <? cnt); apply implM_unr. }
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, SW_SHORT in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold sw_W, STDIO_WRITE_DEPTH in MU.
      unfold zlength in *.
      assert (FD : 0 <= f_fd f < 2^31) by (clear IH; destruct (f_chan f); lia).
      cbn [writev_loop]. apply implM_sys_bind.
      step. if_cases Hc; zify_cond Hc. 1:{ exfalso. clear IH. lia. }
      zs. zs.
      destruct (Z.le_gt_cases cnt (Z.of_nat (length (f_wbuf f)) - k)) as [LE | GT].
      - (* [comment removed for export] *)
        replace (Z.of_nat (length (f_wbuf f)) - k <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
        cbn [advance_iovs]. unfold zlength. rewrite length_skipn.
        replace (Z.of_nat (length (f_wbuf f) - Z.to_nat k) <? cnt) with false by (symmetry; apply Z.ltb_ge; clear IH; lia).
        zs. zs.
        zs. zs. zs. rewrite Z.land_0_l. zs. rewrite Z.sub_0_r. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 2:{ exfalso. clear IH. lia. }
        zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
        zs. zs. zs. zs. zs.
        step_ecall. split.
        { lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
            lazymatch goal with FRM : rw_cells ssegs mm (bv_unsigned sp + -112) _ |- _ =>
              pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [IOV _] end end.
          eapply at_wnode with (A := bv_unsigned sp + -104)
            (iovs := [(Z_to_bv 64 (B + k + cnt), Z_to_bv 64 (Z.of_nat (length (f_wbuf f)) - k - cnt));
                      (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
          - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
            cbn [map concat]. rewrite app_nil_r, length_app, !length_to_bytes, !length_skipn. lia.
          - reflexivity.
          - reflexivity.
          - clear IH; lia.
          - reflexivity.
          - cbn; lia.
          - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
          - clear IH. cbn [map concat]. rewrite app_nil_r, length_app, !length_to_bytes, !length_skipn.
            replace max_write with 67108864 by reflexivity. lia.
          - replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in IOV by lia. exact IOV.
          - constructor; [|constructor; [|constructor]].
            + split; [|split].
              * cbn [snd]. rewrite length_to_bytes, !length_skipn. f_equal. clear IH; lia.
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes, !length_skipn. clear IH; lia.   (* [comment removed for export] *)
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite skipn_skipn.
                replace (Z.to_nat cnt + Z.to_nat k)%nat with (Z.to_nat (k + cnt)) by lia.
                replace (B + k + cnt) with (B + (k + cnt)) by lia. apply buf_at; [exact MU | clear IH; unfold zlength; lia].
            + split; [|split].
              * cbn [snd]. rewrite length_to_bytes. reflexivity.
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes. clear IH; lia.   (* [comment removed for export] *)
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia).
                pose proof (src_at _ 0 MU) as SR. specialize (SR ltac:(clear IH; unfold zlength; lia)). cbn [Z.to_nat skipn] in SR.
                rewrite Z.add_0_r in SR. exact SR. }
       
        intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
        unfold eff0. apply implM_prefix. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x1b50c)) with (Z_to_bv 64 0x1b50c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. zs.
        destruct Hcases as [-> | Hshort].
        + rewrite Z.eqb_refl. if_true.
          apply evt_done. apply implM_ret. apply evt_done.
          unfold sw_ok_post. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
        + replace (cnt' =? Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt) with false by (symmetry; apply Z.eqb_neq; lia).
          if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
          rewrite skipn_skipn.
          replace (Z.to_nat cnt + Z.to_nat k)%nat with (Z.to_nat (k + cnt)) by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt - cnt')
            with (Z.of_nat (length (f_wbuf f)) - (k + cnt) + Z.of_nat (length s) - cnt') by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt)
            with (Z.of_nat (length (f_wbuf f)) - (k + cnt) + Z.of_nat (length s)) in * by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k - cnt) with (Z.of_nat (length (f_wbuf f)) - (k + cnt)) in * by lia.
          replace (B + k + cnt) with (B + (k + cnt)) in * by lia.
          apply evt_done. eapply IH; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | lia | lia | lia].
      - (* [comment removed for export] *)
        replace (Z.of_nat (length (f_wbuf f)) - k <? cnt) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
        cbn [advance_iovs]. unfold zlength. rewrite length_skipn.
        replace (Z.of_nat (length (f_wbuf f) - Z.to_nat k) <? cnt) with true by (symmetry; apply Z.ltb_lt; clear IH; lia).
        zs. zs.
        zs. zs. zs.
        replace (Z.land 18446744073709551615 (Z.of_nat (length (f_wbuf f)) - k)) with (Z.of_nat (length (f_wbuf f)) - k).
        2:{ rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. clear IH; lia. }
        zs. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. clear IH. lia. }
        zs. zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
        zs. zs. zs. zs. zs.
        set (kB := cnt - (Z.of_nat (length (f_wbuf f)) - k)) in *.
        step_ecall. split.
        { lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
            lazymatch goal with FRM : rw_cells ssegs mm (bv_unsigned sp + -112) _ |- _ =>
              pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
          eapply at_wnode with (A := bv_unsigned sp + -88)
            (iovs := [(Z_to_bv 64 (S + kB), Z_to_bv 64 (Z.of_nat (length s) - kB))]).
          - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
            cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn. subst kB. lia.
          - reflexivity.
          - reflexivity.
          - clear IH; lia.
          - cbn [length]. reflexivity.
          - cbn; lia.
          - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
          - clear IH. cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn.
            replace max_write with 67108864 by reflexivity. subst kB. lia.
          - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
          - constructor; [|constructor]. split; [|split].
            + cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. clear IH; subst kB; lia.
            + cbn [fst]. rewrite unsigned_lit by (clear IH; subst kB; lia). rewrite length_to_bytes, length_skipn. clear IH; subst kB; lia.   (* [comment removed for export] *)
            + cbn [fst]. rewrite unsigned_lit by (clear IH; subst kB; lia).
              replace (Z.to_nat (cnt - Z.of_nat (length (f_wbuf f) - Z.to_nat k))) with (Z.to_nat kB) by (subst kB; clear IH; lia).
              apply src_at; [exact MU | clear IH; subst kB; unfold zlength; lia]. }
        intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
        unfold eff0. apply implM_prefix. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x1b50c)) with (Z_to_bv 64 0x1b50c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. zs. 
        replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt) with (Z.of_nat (length s) - kB) in * by (subst kB; lia).
        
        replace (Z.to_nat (cnt - Z.of_nat (length (f_wbuf f) - Z.to_nat k))) with (Z.to_nat kB) by (subst kB; clear IH; lia).
        
        destruct Hcases as [-> | Hshort].
        + rewrite Z.eqb_refl. if_true. 
          apply evt_done. apply implM_ret. apply evt_done.
          unfold sw_ok_post. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
        + replace (cnt' =? Z.of_nat (length s) - kB) with false by (symmetry; apply Z.eqb_neq; lia).
          if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
          cbn [advance_iovs]. 
          replace (zlength (skipn (Z.to_nat kB) s) <? cnt') with false.
          2:{ symmetry. apply Z.ltb_ge. unfold zlength. rewrite length_skipn. clear IH. subst kB. lia. }
          rewrite skipn_skipn.
          replace (Z.to_nat cnt' + Z.to_nat kB)%nat with (Z.to_nat (kB + cnt')) by (clear IH; subst kB; lia).
          replace (Z.of_nat (length s) - kB - cnt') with (Z.of_nat (length s) - kB - cnt') by lia.
          apply evt_done.
          eapply sw_loopB; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | clear IH; subst kB; lia | clear IH; subst kB; lia | clear IH; subst kB; unfold zlength; lia].
    Qed.
  End Loop.
End StdioWrite.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Entry.
  Context {St : Type}.

  Lemma implM_at_eq : forall {A} (c : M St A) s Q ms ms', implM ssegs c s Q ms' -> ms = ms' -> implM ssegs c s Q ms.
  Proof using Type. pin_using tt. intros A c s Q ms ms' H ->. exact H. Qed.

  Ltac ms_eq := cbv delta [mkR]; repeat fastfirst (first [reflexivity | progress f_equal | unfold zlength in *; lia]).

  Definition stdio_write_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn wend readfn writefn seekfn B bufsize prev next : Z)
           (mode : word) (lbf : Z) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells ssegs m Fp (fcells flags rpos rend closefn wend (B + zlength (f_wbuf f)) B readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail) ->
      bytes_at ssegs m B (to_bytes (f_wbuf f)) ->
      bytes_at ssegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31 /\ 1 <= zlength (f_wbuf f) + zlength s)) ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STDIO_WRITE_DEPTH -> 0x55000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv ssegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 <= B -> 0 <= bufsize -> B + bufsize < 2^64 -> B + zlength (f_wbuf f) <= 2^47 ->   (* [comment removed for export] *)
      0 <= S < 2^64 -> S + zlength s <= 2^47 (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      ((B + zlength (f_wbuf f) <= lo \/ bv_unsigned sp <= B) /\ (B + zlength (f_wbuf f) <= Fp + 32 \/ Fp + 64 <= B)) ->
      implM ssegs (stdio_write f s) st
        (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_WRITE) fc None m (seg_rom ssegs)).
  Section Sz13.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn writefn seekfn B bufsize prev next mode lbf tail s S lo canary : ltac2:(SecDiet.SzSec.tyM 'stdio_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma stdio_write_spec__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC BUFB SRC -> -> -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi BWB S0 Shi LENW SEPS SEPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    assert (CH' : if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)).
    { destruct (f_chan f); [exact CH | exact (proj1 CH)]. }
    assert (FD : 0 <= f_fd f < 2^31) by (destruct (f_chan f); lia).
    unfold STDIO_WRITE, STDIO_WRITE_DEPTH in *.
    unfold stdio_write. cbv zeta.
    eapply implM_bind with
      (Q1 := sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend (B + zlength (f_wbuf f)) B
               readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m).
    2:{ intros u st' ms' POST. apply implM_ret.
        eapply sw_tail; [exact POST | lia | lia | lia | exact FSEP1 | exact FSEP2 | lia | lia | lia | ].
        unfold zlength in *. pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC. lia. }
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    unfold fcells, file_cells in FC.
    pose proof (munch_refl (sw_W sp Fp) m) as MU. pose proof (wmono_refl ssegs m) as WM. unfold sw_W, STDIO_WRITE_DEPTH in MU.
    unfold zlength in *.
    assert (LS : length (to_bytes s) = length s) by apply length_to_bytes.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite LS in BSRC.
    change (bytes_at ssegs m S (to_bytes s)) with (boxed (bytes_at ssegs m S (to_bytes s))) in SRC.
    change (bytes_at ssegs m B (to_bytes (f_wbuf f))) with (boxed (bytes_at ssegs m B (to_bytes (f_wbuf f)))) in BUFB.
    cbn [writev_loop].
    destruct (f_wbuf f) as [|b0 wb'] eqn:EWB.
    - (* [comment removed for export] *)
      change (Z.of_nat (@length Z [])) with 0 in *. rewrite !Z.add_0_l in *. rewrite !Z.add_0_r in *.
      apply implM_sys_bind.
      carve_frame 112%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells ssegs ?mm ?A [CB 112 ?j] |- _ =>
        apply (rw_cells_split_CB ssegs mm A [] 112 j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
      do 12 zs. do 13 zs.
      rewrite ?Z.add_0_r. rewrite ?Z.lxor_nilpotent. try change (Z.b2z (0 <? 0)) with 0.
      replace (B - B + Z.of_nat (length s)) with (Z.of_nat (length s)) by lia.
      zs. if_true. zs. zs. rewrite (sx32_small (f_fd f)) by lia. zs. zs. zs. zs.
      step_ecall. split.
      { lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells ssegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
        eapply at_wnode with (A := bv_unsigned sp + -88) (iovs := [(Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
        - generalize CH. destruct (f_chan f); intros CHx; [exact CHx|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, LS. lia.
        - reflexivity.
        - reflexivity.
        - lia.
        - reflexivity.
        - cbn; lia.
        - cbn [length]. lia.   (* [comment removed for export] *)
        - cbn [map concat]. rewrite app_nil_r, LS. replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
        - constructor; [|constructor]. split; [|split].
          + cbn [snd]. rewrite LS. reflexivity.
          + cbn [fst]. rewrite unsigned_lit by lia. rewrite LS. lia.   (* [comment removed for export] *)
          + cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in SRC.
            destruct SEPS as [-> | [SEP1 SEP2]]; [apply bytes_at_nil; lia|].
            apply (bytes_at_transport _ _ _ _ _ _ SRC MU). cbn [disjoint_from]. rewrite LS. lia. }
      intros rsp cnt Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implM_prefix. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x1b484)) with (Z_to_bv 64 0x1b484 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct Hcases as [-> | Hshort].
      + rewrite Z.eqb_refl. step. if_false.
        apply evt_done. apply implM_ret. apply evt_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      + replace (cnt =? Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Hq; zify_cond Hq. 2:{ exfalso. lia. }
        cbn [advance_iovs]. unfold zlength.
        replace (Z.of_nat (length s) <? cnt) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evt_done.
        replace (Z.to_nat cnt) with (Z.to_nat (0 + cnt)) by lia.
        replace (Z.of_nat (length s) - cnt) with (Z.of_nat (length s) - 0 - cnt) by lia.
        replace (C8 (Z_to_bv 64 S)) with (C8 (Z_to_bv 64 (S + 0))) in FR by (do 2 f_equal; lia).
        replace (C8 (Z_to_bv 64 (Z.of_nat (length s)))) with (C8 (Z_to_bv 64 (Z.of_nat (length s) - 0))) in FR by (do 2 f_equal; lia).
        eapply implM_at_eq; [eapply sw_loopB with (k := 0) | ].
        all: try exact FR.
        all: lazymatch goal with |- MS _ _ _ _ _ _ _ = _ => ms_eq | _ => idtac end.
        all: fastfirst (first [ noevar_assumption | unfold fcells, file_cells; exact FC | split; [exact GOT | exact GUARD] | exact SRC | assumption | unfold zlength in *; lia | rewrite EWB; unfold zlength in *; cbn [length Z.of_nat]; lia]).
    - (* [comment removed for export] *)
      rewrite <- EWB in *.
      assert (NB1 : 1 <= Z.of_nat (length (f_wbuf f))) by (rewrite EWB; cbn [length]; lia).
      set (nb := Z.of_nat (length (f_wbuf f))) in *.
      apply implM_sys_bind.
      carve_frame 112%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells ssegs ?mm ?A [CB 112 ?j] |- _ =>
        apply (rw_cells_split_CB ssegs mm A [] 112 j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
      do 12 zs. do 13 zs.
      replace (B + nb - B) with nb in * by lia.
      assert (XNZ : Z.lxor (B + nb) B <> 0) by (intros E; apply Z.lxor_eq in E; lia).
      assert (XNN : 0 <= Z.lxor (B + nb) B) by (apply Z.lxor_nonneg; lia).
      replace (0 <? Z.lxor (B + nb) B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. lia. }
      zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia. zs. zs. zs. zs.
      step_ecall. split.
      { lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells ssegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [IOV _] end end.
        eapply at_wnode with (A := bv_unsigned sp + -104)
          (iovs := [(Z_to_bv 64 B, Z_to_bv 64 nb); (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
        - generalize CH. destruct (f_chan f); intros CHx; [exact CHx|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, length_app, LS, length_to_bytes. lia.
        - reflexivity.
        - reflexivity.
        - lia.
        - reflexivity.
        - cbn; lia.
        - cbn [length]. lia.   (* [comment removed for export] *)
        - cbn [map concat]. rewrite app_nil_r, length_app, LS, length_to_bytes. replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in IOV by lia. exact IOV.
        - constructor; [|constructor; [|constructor]].
          + split; [|split].
            * cbn [snd]. rewrite length_to_bytes. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. rewrite length_to_bytes. subst nb. lia.   (* [comment removed for export] *)
            * cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in BUFB. destruct SEPB as [SEP1 SEP2].
              apply (bytes_at_transport _ _ _ _ _ _ BUFB MU). cbn [disjoint_from]. rewrite length_to_bytes. lia.
          + split; [|split].
            * cbn [snd]. rewrite LS. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. rewrite LS. lia.   (* [comment removed for export] *)
            * cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in SRC.
              destruct SEPS as [-> | [SEP1 SEP2]]; [apply bytes_at_nil; lia|].
              apply (bytes_at_transport _ _ _ _ _ _ SRC MU). cbn [disjoint_from]. rewrite LS. lia. }
      intros rsp cnt Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implM_prefix. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x1b484)) with (Z_to_bv 64 0x1b484 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct Hcases as [-> | Hshort].
      + rewrite Z.eqb_refl. step. if_false.
        apply evt_done. apply implM_ret. apply evt_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      + replace (cnt =? nb + Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Hq; zify_cond Hq. 2:{ exfalso. lia. }
        apply evt_done.
        replace (nb + Z.of_nat (length s) - cnt) with (nb - 0 + Z.of_nat (length s) - cnt) by lia.
        replace (C8 (Z_to_bv 64 B)) with (C8 (Z_to_bv 64 (B + 0))) in FR by (do 2 f_equal; lia).
        replace (C8 (Z_to_bv 64 nb)) with (C8 (Z_to_bv 64 (nb - 0))) in FR by (do 2 f_equal; lia).
          eapply implM_at_eq; [eapply sw_loopA with (k := 0) | ].
        all: try exact FR.
        all: lazymatch goal with |- MS _ _ _ _ _ _ _ = _ => ms_eq | _ => idtac end.
        all: fastfirst (first [ noevar_assumption | unfold fcells, file_cells; exact FC | split; [exact GOT | exact GUARD] | exact SRC | exact BUFB | assumption
                   | subst nb; unfold zlength in *; lia]).
  Qed.
  End Sz13.
  Theorem stdio_write_spec : ltac:(let t := eval cbv delta [stdio_write_spec__stmt] in stdio_write_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn writefn seekfn B bufsize prev next mode lbf tail s S lo canary. ltac2:(SecDiet.SzSec.closeP 'stdio_write_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Entry.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_WRITE : Z := 0x1bbb4.
Definition STDIO_WRITE_DEPTH : Z := 112.
Definition SW_SHORT : Z := 0x1bcd4.   (* [comment removed for export] *)
Definition SW_OK : Z := 0x1bc48.      (* [comment removed for export] *)

(* [comment removed for export] *)
Definition wdec_Some__stmt : Prop := forall f rem rsp cnt,
  wdec f rem rsp = Some cnt ->
  rsp = eff0 (Z_to_bv 64 cnt) /\ 0 <= cnt <= rem /\ 0 <= cnt < 2^64 /\ (cnt = rem \/ 1 <= cnt < rem).
Section Sz1.
Variables f rem rsp cnt : ltac2:(SecDiet.SzSec.tyM 'wdec_Some__stmt "vvvv" @f).
#[using="Type"] Lemma wdec_Some__body : ltac2:(SecDiet.SzSec.bodyP 'wdec_Some__stmt "vvvv").
Proof.
  intros H.
 unfold wdec in H. destruct (f_chan f).
  - apply dec_writev_Some in H as (Hr & -> & Hc). split; [reflexivity|]. lia.
  - unfold dec_writevf_ok, dec_writevf in H.
    destruct (dec_plain (fun v => v =? rem) rsp) as [[e|v]|] eqn:E; try discriminate H.
    injection H as <-. apply dec_plain_Some in E as (-> & Hok & Hv).
    apply Z.eqb_eq in Hok. subst v. split; [reflexivity|]. lia.
Qed.
End Sz1.
Lemma wdec_Some : ltac:(let t := eval cbv delta [wdec_Some__stmt] in wdec_Some__stmt in exact t).
Proof. intros f rem rsp cnt. ltac2:(SecDiet.SzSec.closeP 'wdec_Some__body "vvvv"). Qed.

(* [comment removed for export] *)
Definition at_wnode__stmt : Prop := forall f L (R F : bvmap 5 word) pc fc m (A : Z) (iovs : list (word * word)),
  (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^32 /\ 1 <= Z.of_nat (length (concat (map to_bytes L))))) ->
  reg_get R 10 = Z_to_bv 64 (f_fd f) ->
  reg_get R 11 = Z_to_bv 64 A -> 0 <= A < 2^64 ->
  reg_get R 12 = Z_to_bv 64 (Z.of_nat (length L)) ->
  (1 <= length L <= 2)%nat ->
  A + 16 * Z.of_nat (length L) <= 2^47 ->   (* [comment removed for export] *)
  Z.of_nat (length (concat (map to_bytes L))) <= max_write ->
  bytes_at usegs m A (iovec_bytes iovs) ->
  Forall2 (fun iov bs => snd iov = Z_to_bv 64 (Z.of_nat (length bs)) /\ bv_unsigned (fst iov) + Z.of_nat (length bs) <= 2^47   (* [comment removed for export] *)
                         /\ bytes_at usegs m (bv_unsigned (fst iov)) bs) iovs (map to_bytes L) ->
  at_node usegs (wnode f L) (MSsvc R F pc (Z_to_bv 64 66) fc None m (seg_rom usegs)).
Section Sz2.
Variables f L R F pc fc m A iovs : ltac2:(SecDiet.SzSec.tyM 'at_wnode__stmt "vvvvvvvvv" @f).
#[using="Type"] Lemma at_wnode__body : ltac2:(SecDiet.SzSec.bodyP 'at_wnode__stmt "vvvvvvvvv").
Proof.
  intros CH R10 R11 HA R12 HL HA47 HT HIOV HF.
  unfold wnode. destruct (f_chan f).
  - cbn [at_node]. unfold areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS].
    rewrite R10, R11, R12, length_map. rewrite unsigned_lit by lia.
    repeat split; try reflexivity; try lia. exists iovs. split; assumption.
  - destruct CH as [FD TOT]. cbn [at_node]. unfold areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS].
    rewrite R10, R11, R12, length_map. rewrite unsigned_lit by lia.
    repeat split; try reflexivity; try lia. exists iovs. split; assumption.
Qed.
End Sz2.
Lemma at_wnode : ltac:(let t := eval cbv delta [at_wnode__stmt] in at_wnode__stmt in exact t).
Proof. intros f L R F pc fc m A iovs. ltac2:(SecDiet.SzSec.closeP 'at_wnode__body "vvvvvvvvv"). Qed.

(* [comment removed for export] *)
Definition iov_bytes2__stmt : Prop := forall m A j8 (w0 w1 w2 w3 : word) rest,
  rw_cells usegs m A (CB 8 j8 :: C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: rest) ->
  bytes_at usegs m (A + 8) (iovec_bytes [(w0, w1); (w2, w3)]) /\ bytes_at usegs m (A + 24) (iovec_bytes [(w2, w3)]).
Section Sz3.
Variables m A j8 w0 w1 w2 w3 rest : ltac2:(SecDiet.SzSec.tyM 'iov_bytes2__stmt "vvvvvvvv" @m).
#[using="Type"] Lemma iov_bytes2__body : ltac2:(SecDiet.SzSec.bodyP 'iov_bytes2__stmt "vvvvvvvv").
Proof.
  intros FR.
  destruct FR as [[WF FB] _]. cbn [cells_wf cell_wf] in WF. destruct WF as [L8 _].
  cbn [cells_bytes cbytes] in FB.
  apply bytes_at_app in FB as [_ FB]. rewrite L8 in FB.
  apply bytes_at_app in FB as [FB0 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB3 _].
  cbn [iovec_bytes flat_map fst snd]. rewrite !app_nil_r. split.
  - apply bytes_at_app. rewrite length_app, !length_le8. split.
    + apply bytes_at_app. rewrite length_le8. split.
      * replace (A + 8) with (A + Z.of_nat 8) by lia. exact FB0.
      * replace (A + 8 + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB1.
    + apply bytes_at_app. rewrite length_le8. split.
      * replace (A + 8 + Z.of_nat (8 + 8)) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
      * replace (A + 8 + Z.of_nat (8 + 8) + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
  - apply bytes_at_app. rewrite length_le8. split.
    + replace (A + 24) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
    + replace (A + 24 + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
Qed.
End Sz3.
Lemma iov_bytes2 : ltac:(let t := eval cbv delta [iov_bytes2__stmt] in iov_bytes2__stmt in exact t).
Proof. intros m A j8 w0 w1 w2 w3 rest. ltac2:(SecDiet.SzSec.closeP 'iov_bytes2__body "vvvvvvvv"). Qed.

Lemma length_to_bytes : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros. unfold to_bytes. rewrite skipn_map. reflexivity. Qed.

Lemma bytes_at_skipn : forall m A bs n, bytes_at usegs m A bs -> (n <= length bs)%nat ->
  bytes_at usegs m (A + Z.of_nat n) (skipn n bs).
Proof.
  intros m A bs n H Hn. rewrite <- (firstn_skipn n bs) in H. apply bytes_at_app in H as [_ H].
  rewrite firstn_length_le in H by lia. exact H.
Qed.

Section StdioWrite.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition fcells (flags : word) (rpos rend closefn : Z) (wend wpos wbase : Z)
      (readfn writefn seekfn B bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
    file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next fd mode lbf tail.

  Definition sw_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - STDIO_WRITE_DEPTH, bv_unsigned sp); (Fp + 32, Fp + 64)].

  (* [comment removed for export] *)
  Definition stdio_write_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn readfn writefn seekfn B bufsize prev next : Z) (mode : word) (lbf : Z) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => f' = set_w true [] f /\ st' = st /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch (sw_W sp Fp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' Fp (fcells flags rpos rend closefn (B + bufsize) B B readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail)
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition sw_ok_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z) (mode : word) (lbf : Z) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : unit -> St -> machine_state -> Prop :=
    fun _ st' ms' => st' = st /\
      exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x22 t3 t4 t5 t6 : word) (j8 : list byte) (w0 w1 w2 w3 : word) (m' : mem),
      ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp) a0 a1 a2 a3 a4 a5 a6 a7
                    x18 x19 x20 (Z_to_bv 64 ssp_guard) x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 SW_OK) fc None m' (seg_rom usegs)
      /\ munch (sw_W sp Fp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp + -112)
      /\ rw_cells usegs m' (bv_unsigned sp + -112)
           [CB 8 j8; C8 w0; C8 w1; C8 w2; C8 w3; C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ rw_cells usegs m' Fp (fcells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail)
      /\ ssp_cells m' canary.

  (* [comment removed for export] *)
  Definition sw_tail__stmt : Prop := forall (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st st' : St) (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z)
      (mode : word) (lbf : Z) (tail : list byte) (len lo : Z) (canary : word) (m : mem) ms u,
    sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m u st' ms ->
    (0 <= Fp) -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) -> (lo <= bv_unsigned sp - 112) ->
    (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
    (0 <= B) -> (0 <= bufsize) -> (B + bufsize < 2^64) -> (0 <= len < 2^64) ->
    evt usegs (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m (set_w true [] f) st') ms.
  Section Sz7.
  Variables ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st st' Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m ms u : ltac2:(SecDiet.SzSec.tyM 'sw_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma sw_tail__body : ltac2:(SecDiet.SzSec.bodyP 'sw_tail__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros POST Fp0 FPLO LO FSEP1 FSEP2 B0 BS0 BShi LEN.
    destruct POST as [-> POST]. destruct_exs POST.
    destruct POST as (-> & MU & WM & MI & ST & FR & FC & [GOT GUARD]).
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    unfold fcells, file_cells in FC. unfold got_ssp, ssp_guard, SW_OK in *.
    rename x23 into m1. unfold sw_W, STDIO_WRITE_DEPTH in MU.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. cbn [cells_size csize Nat.add] in FB.
    do 7 step.
    (* [comment removed for export] *)
    step. step. step. if_false.
    do 10 step.
    release_frame FR ST (bv_unsigned sp).
    apply evt_done. unfold stdio_write_post, fcells, file_cells. split; [reflexivity|]. split; [reflexivity|].
    sys_finish. split; [exact GOT | exact GUARD].
  Qed.
  End Sz7.
  Lemma sw_tail : ltac:(let t := eval cbv delta [sw_tail__stmt] in sw_tail__stmt in exact t).
  Proof using Type. intros ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st st' Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next mode lbf tail len lo canary m ms u. ltac2:(SecDiet.SzSec.closeP 'sw_tail__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Section Loop.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next : Z)
              (mode : word) (lbf : Z) (tail : list byte) (s : list Z) (S lo : Z) (canary : word) (m : mem).
    #[local] Notation len := (zlength s) (only parsing).
    #[local] Notation wb := (f_wbuf f) (only parsing).
    #[local] Notation FCELLS := (fcells flags rpos rend closefn wend wpos wbase readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail) (only parsing).
    #[local] Notation QOK := (sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend wpos wbase
                 readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m) (only parsing).

    Hypothesis CH : if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31).
    Hypothesis LO : lo <= bv_unsigned sp - 112.
    Hypothesis SP47 : bv_unsigned sp <= 2^47.   (* [comment removed for export] *)
    Hypothesis GLO : 0x56000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo \/ bv_unsigned sp <= Fp.
    Hypothesis S0 : 0 <= S < 2^64.
    Hypothesis Shi : S + len <= 2^47.   (* [comment removed for export] *)
    Hypothesis LENW : zlength wb + len <= 2^26.
    Hypothesis SEPS : s = [] \/ ((S + len <= lo \/ bv_unsigned sp <= S) /\ (S + len <= Fp + 32 \/ Fp + 64 <= S)).
    Hypothesis SRC : bytes_at usegs m S (to_bytes s).      (* [comment removed for export] *)
    Hypothesis B0 : 0 <= B.
    Hypothesis BWB : B + zlength wb <= 2^47.   (* [comment removed for export] *)
    Hypothesis SEPB : (B + zlength wb <= lo \/ bv_unsigned sp <= B) /\ (B + zlength wb <= Fp + 32 \/ Fp + 64 <= B).
    Hypothesis BUFB : bytes_at usegs m B (to_bytes wb).    (* [comment removed for export] *)

    Definition src_at__stmt : Prop := forall m1 k, munch (sw_W sp Fp) m m1 -> 0 <= k <= len ->
      bytes_at usegs m1 (S + k) (to_bytes (skipn (Z.to_nat k) s)).
    Section Sz8.
    Variables m1 k : ltac2:(SecDiet.SzSec.tyM 'src_at__stmt "vv" @m1).
    Lemma src_at__body : ltac2:(SecDiet.SzSec.bodyP 'src_at__stmt "vv").
    Proof using FPLO LENW LO S0 SEPB SEPS SRC Shi. pin_using (fun (FPLO LENW LO S0 SEPB SEPS SRC Shi : unit) => tt).
      intros MU Hk.
 rewrite to_bytes_skipn.
      replace (S + k) with (S + Z.of_nat (Z.to_nat k)) by lia.
      apply bytes_at_skipn; [| rewrite length_to_bytes; unfold zlength in Hk; lia].
      destruct SEPS as [-> | [SEP1 SEP2]].
      - apply bytes_at_nil. lia.
      - apply (bytes_at_transport _ _ _ m1 _ _ SRC MU). unfold sw_W, STDIO_WRITE_DEPTH. cbn [disjoint_from].
        rewrite length_to_bytes. unfold zlength in *. lia.
    Qed.
    End Sz8.
    Lemma src_at : ltac:(let t := eval cbv delta [src_at__stmt] in src_at__stmt in exact t).
    Proof using FPLO LENW LO S0 SEPB SEPS SRC Shi. intros m1 k. ltac2:(SecDiet.SzSec.closeP 'src_at__body "vv"). Qed.

    Definition buf_at__stmt : Prop := forall m1 k, munch (sw_W sp Fp) m m1 -> 0 <= k <= zlength wb ->
      bytes_at usegs m1 (B + k) (to_bytes (skipn (Z.to_nat k) wb)).
    Section Sz9.
    Variables m1 k : ltac2:(SecDiet.SzSec.tyM 'buf_at__stmt "vv" @m1).
    Lemma buf_at__body : ltac2:(SecDiet.SzSec.bodyP 'buf_at__stmt "vv").
    Proof using B0 BUFB BWB FPLO LENW LO SEPB SP47. pin_using (fun (B0 BUFB BWB FPLO LENW LO SEPB SP47 : unit) => tt).
      intros MU Hk.
 rewrite to_bytes_skipn.
      replace (B + k) with (B + Z.of_nat (Z.to_nat k)) by lia.
      apply bytes_at_skipn; [| rewrite length_to_bytes; unfold zlength in Hk; lia].
      destruct (f_wbuf f) as [|b0 wb'] eqn:EWB.
      - apply bytes_at_nil. lia.
      - destruct SEPB as [SEP1 SEP2].
        apply (bytes_at_transport _ _ _ m1 _ _ BUFB MU). unfold sw_W, STDIO_WRITE_DEPTH. cbn [disjoint_from].
        rewrite length_to_bytes. unfold zlength in *. cbn [length] in *. lia.
    Qed.
    End Sz9.
    Lemma buf_at : ltac:(let t := eval cbv delta [buf_at__stmt] in buf_at__stmt in exact t).
    Proof using B0 BUFB BWB FPLO LENW LO SEPB SP47. intros m1 k. ltac2:(SecDiet.SzSec.closeP 'buf_at__body "vv"). Qed.

    (* [comment removed for export] *)
    Lemma sw_loopB : forall fuel (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (j8 : list byte) (w0 w1 : word)
        (k cnt : Z) (m1 : mem),
      rw_cells usegs m1 (bv_unsigned sp + -112)
        [CB 8 j8; C8 w0; C8 w1; C8 (Z_to_bv 64 (S + k)); C8 (Z_to_bv 64 (len - k)); C8 canary; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m1 Fp FCELLS ->
      ssp_cells m1 canary -> stk usegs m1 lo (bv_unsigned sp + -112) -> mem_inv usegs m1 ->
      munch (sw_W sp Fp) m m1 -> wmono usegs m m1 ->
      0 <= k -> 1 <= cnt -> k + cnt < len ->
      implM usegs (writev_loop fuel f [skipn (Z.to_nat (k + cnt)) s] (len - k - cnt)) st QOK
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 cnt) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -88)) x20 (Z_to_bv 64 ssp_guard) (Z_to_bv 64 (len - k))
                 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SW_SHORT) fc None m1 (seg_rom usegs)).
    Proof using CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi. pin_using (fun (CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi : unit) => tt).
      induction fuel as [|fuel IH]; intros until m1; intros FR FC SSP ST MI MU WM K0 C1 KC.
      { cbn [writev_loop]. apply implM_unr. }
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, SW_SHORT in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold sw_W, STDIO_WRITE_DEPTH in MU.
      cbn [writev_loop]. apply implM_sys_bind.
      unfold zlength in *.
      assert (LS : Z.of_nat (length (to_bytes s)) = Z.of_nat (length s)) by (rewrite length_to_bytes; reflexivity).
      step. if_cases Hc; zify_cond Hc. 1:{ exfalso. clear IH. lia. }
      zs. zs.
      replace (Z.of_nat (length s) - k <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
      assert (FD : 0 <= f_fd f < 2^31) by (clear IH; destruct (f_chan f); lia).
      zs. zs.
      zs. zs. zs. rewrite Z.land_0_l. zs. rewrite Z.sub_0_r. zs. zs.
      zs. if_cases Hb; zify_cond Hb. 2:{ exfalso. clear IH. lia. }
      zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
      zs. zs. zs. zs. zs.
      step_ecall. split.
      { (* [comment removed for export] *)
        lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells usegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
        eapply at_wnode with (A := bv_unsigned sp + -88)
          (iovs := [(Z_to_bv 64 (S + k + cnt), Z_to_bv 64 (Z.of_nat (length s) - k - cnt))]).
        - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn. lia.
        - reflexivity.
        - reflexivity.
        - clear IH; lia.
        - reflexivity.
        - cbn; lia.
        - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
        - clear IH. cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn.
          replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
        - constructor; [|constructor]. split; [|split].
          + cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. clear IH; lia.
          + cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes, length_skipn. clear IH; lia.   (* [comment removed for export] *)
          + cbn [fst]. rewrite unsigned_lit by (clear IH; lia).
            replace (S + k + cnt) with (S + (k + cnt)) by lia. apply src_at; [exact MU | clear IH; unfold zlength; lia]. }
      (* [comment removed for export] *)
      intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implM_prefix. sys_nret.
      (* [comment removed for export] *)
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x1bccc)) with (Z_to_bv 64 0x1bccc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zs. zs.
      destruct Hcases as [-> | Hshort].
      - (* [comment removed for export] *)
        rewrite Z.eqb_refl. if_true.
        apply evt_done. apply implM_ret. apply evt_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      - (* [comment removed for export] *)
        replace (cnt' =? Z.of_nat (length s) - k - cnt) with false by (symmetry; apply Z.eqb_neq; lia).
        if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
        cbn [advance_iovs].
        replace (zlength (skipn (Z.to_nat (k + cnt)) s) <? cnt') with false.
        2:{ symmetry. apply Z.ltb_ge. unfold zlength. rewrite length_skipn. clear IH. lia. }
        rewrite skipn_skipn.
        replace (Z.to_nat cnt' + Z.to_nat (k + cnt))%nat with (Z.to_nat ((k + cnt) + cnt')) by lia.
        replace (Z.of_nat (length s) - k - cnt - cnt') with (Z.of_nat (length s) - (k + cnt) - cnt') by lia.
        replace (Z.of_nat (length s) - k - cnt) with (Z.of_nat (length s) - (k + cnt)) in * by lia.
        replace (S + k + cnt) with (S + (k + cnt)) in * by lia.
        apply evt_done. eapply IH; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | lia | lia | lia].
    Qed.

    (* [comment removed for export] *)
    Lemma sw_loopA : forall fuel (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x20 t3 t4 t5 t6 : word) (j8 : list byte)
        (k cnt : Z) (m1 : mem),
      rw_cells usegs m1 (bv_unsigned sp + -112)
        [CB 8 j8; C8 (Z_to_bv 64 (B + k)); C8 (Z_to_bv 64 (zlength wb - k)); C8 (Z_to_bv 64 S); C8 (Z_to_bv 64 len); C8 canary;
         C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m1 Fp FCELLS ->
      ssp_cells m1 canary -> stk usegs m1 lo (bv_unsigned sp + -112) -> mem_inv usegs m1 ->
      munch (sw_W sp Fp) m m1 -> wmono usegs m m1 ->
      0 <= k <= zlength wb -> 1 <= cnt -> k + cnt < zlength wb + len ->
      implM usegs (writev_loop fuel f (advance_iovs [skipn (Z.to_nat k) wb; s] cnt) (zlength wb - k + len - cnt)) st QOK
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp t0 t1 t2 (Z_to_bv 64 len) (Z_to_bv 64 Fp)
                 (Z_to_bv 64 cnt) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 2) (Z_to_bv 64 (bv_unsigned sp + -104)) x20 (Z_to_bv 64 ssp_guard)
                 (Z_to_bv 64 (zlength wb - k + len)) s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 SW_SHORT) fc None m1 (seg_rom usegs)).
    Proof using B0 BUFB BWB CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi. pin_using (fun (B0 BUFB BWB CH FPLO GLO LENW LO S0 SEPB SEPS SP47 SRC Shi : unit) => tt).
      induction fuel as [|fuel IH]; intros until m1; intros FR FC SSP ST MI MU WM K0 C1 KC.
      { cbn [writev_loop]. destruct (zlength (skipn (Z.to_nat k) wb) <? cnt); apply implM_unr. }
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, SW_SHORT in *.
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold sw_W, STDIO_WRITE_DEPTH in MU.
      unfold zlength in *.
      assert (FD : 0 <= f_fd f < 2^31) by (clear IH; destruct (f_chan f); lia).
      cbn [writev_loop]. apply implM_sys_bind.
      step. if_cases Hc; zify_cond Hc. 1:{ exfalso. clear IH. lia. }
      zs. zs.
      destruct (Z.le_gt_cases cnt (Z.of_nat (length (f_wbuf f)) - k)) as [LE | GT].
      - (* [comment removed for export] *)
        replace (Z.of_nat (length (f_wbuf f)) - k <? cnt) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z].
        cbn [advance_iovs]. unfold zlength. rewrite length_skipn.
        replace (Z.of_nat (length (f_wbuf f) - Z.to_nat k) <? cnt) with false by (symmetry; apply Z.ltb_ge; clear IH; lia).
        zs. zs.
        zs. zs. zs. rewrite Z.land_0_l. zs. rewrite Z.sub_0_r. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 2:{ exfalso. clear IH. lia. }
        zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
        zs. zs. zs. zs. zs.
        step_ecall. split.
        { lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
            lazymatch goal with FRM : rw_cells usegs mm (bv_unsigned sp + -112) _ |- _ =>
              pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [IOV _] end end.
          eapply at_wnode with (A := bv_unsigned sp + -104)
            (iovs := [(Z_to_bv 64 (B + k + cnt), Z_to_bv 64 (Z.of_nat (length (f_wbuf f)) - k - cnt));
                      (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
          - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
            cbn [map concat]. rewrite app_nil_r, length_app, !length_to_bytes, !length_skipn. lia.
          - reflexivity.
          - reflexivity.
          - clear IH; lia.
          - reflexivity.
          - cbn; lia.
          - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
          - clear IH. cbn [map concat]. rewrite app_nil_r, length_app, !length_to_bytes, !length_skipn.
            replace max_write with 67108864 by reflexivity. lia.
          - replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in IOV by lia. exact IOV.
          - constructor; [|constructor; [|constructor]].
            + split; [|split].
              * cbn [snd]. rewrite length_to_bytes, !length_skipn. f_equal. clear IH; lia.
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes, !length_skipn. clear IH; lia.   (* [comment removed for export] *)
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite skipn_skipn.
                replace (Z.to_nat cnt + Z.to_nat k)%nat with (Z.to_nat (k + cnt)) by lia.
                replace (B + k + cnt) with (B + (k + cnt)) by lia. apply buf_at; [exact MU | clear IH; unfold zlength; lia].
            + split; [|split].
              * cbn [snd]. rewrite length_to_bytes. reflexivity.
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia). rewrite length_to_bytes. clear IH; lia.   (* [comment removed for export] *)
              * cbn [fst]. rewrite unsigned_lit by (clear IH; lia).
                pose proof (src_at _ 0 MU) as SR. specialize (SR ltac:(clear IH; unfold zlength; lia)). cbn [Z.to_nat skipn] in SR.
                rewrite Z.add_0_r in SR. exact SR. }
       
        intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
        unfold eff0. apply implM_prefix. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x1bccc)) with (Z_to_bv 64 0x1bccc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. zs.
        destruct Hcases as [-> | Hshort].
        + rewrite Z.eqb_refl. if_true.
          apply evt_done. apply implM_ret. apply evt_done.
          unfold sw_ok_post. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
        + replace (cnt' =? Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt) with false by (symmetry; apply Z.eqb_neq; lia).
          if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
          rewrite skipn_skipn.
          replace (Z.to_nat cnt + Z.to_nat k)%nat with (Z.to_nat (k + cnt)) by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt - cnt')
            with (Z.of_nat (length (f_wbuf f)) - (k + cnt) + Z.of_nat (length s) - cnt') by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt)
            with (Z.of_nat (length (f_wbuf f)) - (k + cnt) + Z.of_nat (length s)) in * by lia.
          replace (Z.of_nat (length (f_wbuf f)) - k - cnt) with (Z.of_nat (length (f_wbuf f)) - (k + cnt)) in * by lia.
          replace (B + k + cnt) with (B + (k + cnt)) in * by lia.
          apply evt_done. eapply IH; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | lia | lia | lia].
      - (* [comment removed for export] *)
        replace (Z.of_nat (length (f_wbuf f)) - k <? cnt) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
        cbn [advance_iovs]. unfold zlength. rewrite length_skipn.
        replace (Z.of_nat (length (f_wbuf f) - Z.to_nat k) <? cnt) with true by (symmetry; apply Z.ltb_lt; clear IH; lia).
        zs. zs.
        zs. zs. zs.
        replace (Z.land 18446744073709551615 (Z.of_nat (length (f_wbuf f)) - k)) with (Z.of_nat (length (f_wbuf f)) - k).
        2:{ rewrite Z.land_comm. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia. symmetry. apply Z.mod_small. clear IH; lia. }
        zs. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. clear IH. lia. }
        zs. zs. zs. zs. zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia.
        zs. zs. zs. zs. zs.
        set (kB := cnt - (Z.of_nat (length (f_wbuf f)) - k)) in *.
        step_ecall. split.
        { lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
            lazymatch goal with FRM : rw_cells usegs mm (bv_unsigned sp + -112) _ |- _ =>
              pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
          eapply at_wnode with (A := bv_unsigned sp + -88)
            (iovs := [(Z_to_bv 64 (S + kB), Z_to_bv 64 (Z.of_nat (length s) - kB))]).
          - clear IH. generalize CH. destruct (f_chan f); intros CH'; [exact CH'|]. split; [lia|].
            cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn. subst kB. lia.
          - reflexivity.
          - reflexivity.
          - clear IH; lia.
          - cbn [length]. reflexivity.
          - cbn; lia.
          - clear IH. cbn [length]. lia.   (* [comment removed for export] *)
          - clear IH. cbn [map concat]. rewrite app_nil_r, length_to_bytes, length_skipn.
            replace max_write with 67108864 by reflexivity. subst kB. lia.
          - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
          - constructor; [|constructor]. split; [|split].
            + cbn [snd]. rewrite length_to_bytes, length_skipn. f_equal. clear IH; subst kB; lia.
            + cbn [fst]. rewrite unsigned_lit by (clear IH; subst kB; lia). rewrite length_to_bytes, length_skipn. clear IH; subst kB; lia.   (* [comment removed for export] *)
            + cbn [fst]. rewrite unsigned_lit by (clear IH; subst kB; lia).
              replace (Z.to_nat (cnt - Z.of_nat (length (f_wbuf f) - Z.to_nat k))) with (Z.to_nat kB) by (subst kB; clear IH; lia).
              apply src_at; [exact MU | clear IH; subst kB; unfold zlength; lia]. }
        intros rsp cnt' Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
        unfold eff0. apply implM_prefix. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. clear IH. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x1bccc)) with (Z_to_bv 64 0x1bccc : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. zs. 
        replace (Z.of_nat (length (f_wbuf f)) - k + Z.of_nat (length s) - cnt) with (Z.of_nat (length s) - kB) in * by (subst kB; lia).
        
        replace (Z.to_nat (cnt - Z.of_nat (length (f_wbuf f) - Z.to_nat k))) with (Z.to_nat kB) by (subst kB; clear IH; lia).
        
        destruct Hcases as [-> | Hshort].
        + rewrite Z.eqb_refl. if_true. 
          apply evt_done. apply implM_ret. apply evt_done.
          unfold sw_ok_post. split; [reflexivity|].
          repeat (lazymatch goal with |- ex _ => eexists end).
          split; [cbv delta [mkR]; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
        + replace (cnt' =? Z.of_nat (length s) - kB) with false by (symmetry; apply Z.eqb_neq; lia).
          if_cases Hq; zify_cond Hq. 1:{ exfalso. clear IH. lia. }
          cbn [advance_iovs]. 
          replace (zlength (skipn (Z.to_nat kB) s) <? cnt') with false.
          2:{ symmetry. apply Z.ltb_ge. unfold zlength. rewrite length_skipn. clear IH. subst kB. lia. }
          rewrite skipn_skipn.
          replace (Z.to_nat cnt' + Z.to_nat kB)%nat with (Z.to_nat (kB + cnt')) by (clear IH; subst kB; lia).
          replace (Z.of_nat (length s) - kB - cnt') with (Z.of_nat (length s) - kB - cnt') by lia.
          apply evt_done.
          eapply sw_loopB; [exact FR | unfold fcells, file_cells; exact FC | split; [exact GOT|exact GUARD] | exact ST | exact MI | exact MU | exact WM | clear IH; subst kB; lia | clear IH; subst kB; lia | clear IH; subst kB; unfold zlength; lia].
    Qed.
  End Loop.
End StdioWrite.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Entry.
  Context {St : Type}.

  Lemma implM_at_eq : forall {A} (c : M St A) s Q ms ms', implM usegs c s Q ms' -> ms = ms' -> implM usegs c s Q ms.
  Proof using Type. pin_using tt. intros A c s Q ms ms' H ->. exact H. Qed.

  Ltac ms_eq := cbv delta [mkR]; repeat fastfirst (first [reflexivity | progress f_equal | unfold zlength in *; lia]).

  Definition stdio_write_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn wend readfn writefn seekfn B bufsize prev next : Z)
           (mode : word) (lbf : Z) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells usegs m Fp (fcells flags rpos rend closefn wend (B + zlength (f_wbuf f)) B readfn writefn seekfn B bufsize prev next (f_fd f) mode lbf tail) ->
      bytes_at usegs m B (to_bytes (f_wbuf f)) ->
      bytes_at usegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31 /\ 1 <= zlength (f_wbuf f) + zlength s)) ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STDIO_WRITE_DEPTH -> 0x56000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv usegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 <= B -> 0 <= bufsize -> B + bufsize < 2^64 -> B + zlength (f_wbuf f) <= 2^47 ->   (* [comment removed for export] *)
      0 <= S < 2^64 -> S + zlength s <= 2^47 (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp + 32 \/ Fp + 64 <= S))) ->
      ((B + zlength (f_wbuf f) <= lo \/ bv_unsigned sp <= B) /\ (B + zlength (f_wbuf f) <= Fp + 32 \/ Fp + 64 <= B)) ->
      implM usegs (stdio_write f s) st
        (stdio_write_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_WRITE) fc None m (seg_rom usegs)).
  Section Sz13.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn writefn seekfn B bufsize prev next mode lbf tail s S lo canary : ltac2:(SecDiet.SzSec.tyM 'stdio_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma stdio_write_spec__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_write_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros FC BUFB SRC -> -> -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi BWB S0 Shi LENW SEPS SEPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    assert (CH' : if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)).
    { destruct (f_chan f); [exact CH | exact (proj1 CH)]. }
    assert (FD : 0 <= f_fd f < 2^31) by (destruct (f_chan f); lia).
    unfold STDIO_WRITE, STDIO_WRITE_DEPTH in *.
    unfold stdio_write. cbv zeta.
    eapply implM_bind with
      (Q1 := sw_ok_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn wend (B + zlength (f_wbuf f)) B
               readfn writefn seekfn B bufsize prev next mode lbf tail (zlength s) lo canary m).
    2:{ intros u st' ms' POST. apply implM_ret.
        eapply sw_tail; [exact POST | lia | lia | lia | exact FSEP1 | exact FSEP2 | lia | lia | lia | ].
        unfold zlength in *. pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite length_to_bytes in BSRC. lia. }
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    unfold fcells, file_cells in FC.
    pose proof (munch_refl (sw_W sp Fp) m) as MU. pose proof (wmono_refl usegs m) as WM. unfold sw_W, STDIO_WRITE_DEPTH in MU.
    unfold zlength in *.
    assert (LS : length (to_bytes s) = length s) by apply length_to_bytes.
    pose proof (bytes_at_bound _ _ _ _ SRC) as BSRC. rewrite LS in BSRC.
    change (bytes_at usegs m S (to_bytes s)) with (boxed (bytes_at usegs m S (to_bytes s))) in SRC.
    change (bytes_at usegs m B (to_bytes (f_wbuf f))) with (boxed (bytes_at usegs m B (to_bytes (f_wbuf f)))) in BUFB.
    cbn [writev_loop].
    destruct (f_wbuf f) as [|b0 wb'] eqn:EWB.
    - (* [comment removed for export] *)
      change (Z.of_nat (@length Z [])) with 0 in *. rewrite !Z.add_0_l in *. rewrite !Z.add_0_r in *.
      apply implM_sys_bind.
      carve_frame 112%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells usegs ?mm ?A [CB 112 ?j] |- _ =>
        apply (rw_cells_split_CB usegs mm A [] 112 j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
      do 12 zs. do 13 zs.
      rewrite ?Z.add_0_r. rewrite ?Z.lxor_nilpotent. try change (Z.b2z (0 <? 0)) with 0.
      replace (B - B + Z.of_nat (length s)) with (Z.of_nat (length s)) by lia.
      zs. if_true. zs. zs. rewrite (sx32_small (f_fd f)) by lia. zs. zs. zs. zs.
      step_ecall. split.
      { lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells usegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [_ IOV] end end.
        eapply at_wnode with (A := bv_unsigned sp + -88) (iovs := [(Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
        - generalize CH. destruct (f_chan f); intros CHx; [exact CHx|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, LS. lia.
        - reflexivity.
        - reflexivity.
        - lia.
        - reflexivity.
        - cbn; lia.
        - cbn [length]. lia.   (* [comment removed for export] *)
        - cbn [map concat]. rewrite app_nil_r, LS. replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 24) with (bv_unsigned sp + -88) in IOV by lia. exact IOV.
        - constructor; [|constructor]. split; [|split].
          + cbn [snd]. rewrite LS. reflexivity.
          + cbn [fst]. rewrite unsigned_lit by lia. rewrite LS. lia.   (* [comment removed for export] *)
          + cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in SRC.
            destruct SEPS as [-> | [SEP1 SEP2]]; [apply bytes_at_nil; lia|].
            apply (bytes_at_transport _ _ _ _ _ _ SRC MU). cbn [disjoint_from]. rewrite LS. lia. }
      intros rsp cnt Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implM_prefix. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x1bc44)) with (Z_to_bv 64 0x1bc44 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct Hcases as [-> | Hshort].
      + rewrite Z.eqb_refl. step. if_false.
        apply evt_done. apply implM_ret. apply evt_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      + replace (cnt =? Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Hq; zify_cond Hq. 2:{ exfalso. lia. }
        cbn [advance_iovs]. unfold zlength.
        replace (Z.of_nat (length s) <? cnt) with false by (symmetry; apply Z.ltb_ge; lia).
        apply evt_done.
        replace (Z.to_nat cnt) with (Z.to_nat (0 + cnt)) by lia.
        replace (Z.of_nat (length s) - cnt) with (Z.of_nat (length s) - 0 - cnt) by lia.
        replace (C8 (Z_to_bv 64 S)) with (C8 (Z_to_bv 64 (S + 0))) in FR by (do 2 f_equal; lia).
        replace (C8 (Z_to_bv 64 (Z.of_nat (length s)))) with (C8 (Z_to_bv 64 (Z.of_nat (length s) - 0))) in FR by (do 2 f_equal; lia).
        eapply implM_at_eq; [eapply sw_loopB with (k := 0) | ].
        all: try exact FR.
        all: lazymatch goal with |- MS _ _ _ _ _ _ _ = _ => ms_eq | _ => idtac end.
        all: fastfirst (first [ noevar_assumption | unfold fcells, file_cells; exact FC | split; [exact GOT | exact GUARD] | exact SRC | assumption | unfold zlength in *; lia | rewrite EWB; unfold zlength in *; cbn [length Z.of_nat]; lia]).
    - (* [comment removed for export] *)
      rewrite <- EWB in *.
      assert (NB1 : 1 <= Z.of_nat (length (f_wbuf f))) by (rewrite EWB; cbn [length]; lia).
      set (nb := Z.of_nat (length (f_wbuf f))) in *.
      apply implM_sys_bind.
      carve_frame 112%nat ST.
    (* [comment removed for export] *)
    lazymatch goal with
    | FRx : rw_cells usegs ?mm ?A [CB 112 ?j] |- _ =>
        apply (rw_cells_split_CB usegs mm A [] 112 j [] [8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8; 8]%nat) in FRx; [ | reflexivity ];
        cbn [app mk_CB_cells] in FRx;
        repeat match type of FRx with
        | context [CB _ ?p] => lazymatch p with firstn _ _ => let jx := fresh "jk" in set (jx := p) in FRx; clearbody jx end
        end
    end.
      do 12 zs. do 13 zs.
      replace (B + nb - B) with nb in * by lia.
      assert (XNZ : Z.lxor (B + nb) B <> 0) by (intros E; apply Z.lxor_eq in E; lia).
      assert (XNN : 0 <= Z.lxor (B + nb) B) by (apply Z.lxor_nonneg; lia).
      replace (0 <? Z.lxor (B + nb) B) with true by (symmetry; apply Z.ltb_lt; lia). cbn [Z.b2z].
      zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. lia. }
      zs. zs. zs. rewrite (sx32_small (f_fd f)) by lia. zs. zs. zs. zs.
      step_ecall. split.
      { lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells usegs mm (bv_unsigned sp + -112) _ |- _ =>
            pose proof (iov_bytes2 _ _ _ _ _ _ _ _ FRM) as [IOV _] end end.
        eapply at_wnode with (A := bv_unsigned sp + -104)
          (iovs := [(Z_to_bv 64 B, Z_to_bv 64 nb); (Z_to_bv 64 S, Z_to_bv 64 (Z.of_nat (length s)))]).
        - generalize CH. destruct (f_chan f); intros CHx; [exact CHx|]. split; [lia|].
          cbn [map concat]. rewrite app_nil_r, length_app, LS, length_to_bytes. lia.
        - reflexivity.
        - reflexivity.
        - lia.
        - reflexivity.
        - cbn; lia.
        - cbn [length]. lia.   (* [comment removed for export] *)
        - cbn [map concat]. rewrite app_nil_r, length_app, LS, length_to_bytes. replace max_write with 67108864 by reflexivity. lia.
        - replace (bv_unsigned sp + -112 + 8) with (bv_unsigned sp + -104) in IOV by lia. exact IOV.
        - constructor; [|constructor; [|constructor]].
          + split; [|split].
            * cbn [snd]. rewrite length_to_bytes. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. rewrite length_to_bytes. subst nb. lia.   (* [comment removed for export] *)
            * cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in BUFB. destruct SEPB as [SEP1 SEP2].
              apply (bytes_at_transport _ _ _ _ _ _ BUFB MU). cbn [disjoint_from]. rewrite length_to_bytes. lia.
          + split; [|split].
            * cbn [snd]. rewrite LS. reflexivity.
            * cbn [fst]. rewrite unsigned_lit by lia. rewrite LS. lia.   (* [comment removed for export] *)
            * cbn [fst]. rewrite unsigned_lit by lia. unfold boxed in SRC.
              destruct SEPS as [-> | [SEP1 SEP2]]; [apply bytes_at_nil; lia|].
              apply (bytes_at_transport _ _ _ _ _ _ SRC MU). cbn [disjoint_from]. rewrite LS. lia. }
      intros rsp cnt Hdec. apply wdec_Some in Hdec as (-> & Hc1 & Hc2 & Hcases).
      unfold eff0. apply implM_prefix. sys_nret.
      step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
      step.
      replace (ret_pc (Z_to_bv 64 0x1bc44)) with (Z_to_bv 64 0x1bc44 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      destruct Hcases as [-> | Hshort].
      + rewrite Z.eqb_refl. step. if_false.
        apply evt_done. apply implM_ret. apply evt_done.
        unfold sw_ok_post. split; [reflexivity|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        split; [exact FR|]. split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT|exact GUARD].
      + replace (cnt =? nb + Z.of_nat (length s)) with false by (symmetry; apply Z.eqb_neq; lia).
        step. if_cases Hq; zify_cond Hq. 2:{ exfalso. lia. }
        apply evt_done.
        replace (nb + Z.of_nat (length s) - cnt) with (nb - 0 + Z.of_nat (length s) - cnt) by lia.
        replace (C8 (Z_to_bv 64 B)) with (C8 (Z_to_bv 64 (B + 0))) in FR by (do 2 f_equal; lia).
        replace (C8 (Z_to_bv 64 nb)) with (C8 (Z_to_bv 64 (nb - 0))) in FR by (do 2 f_equal; lia).
          eapply implM_at_eq; [eapply sw_loopA with (k := 0) | ].
        all: try exact FR.
        all: lazymatch goal with |- MS _ _ _ _ _ _ _ = _ => ms_eq | _ => idtac end.
        all: fastfirst (first [ noevar_assumption | unfold fcells, file_cells; exact FC | split; [exact GOT | exact GUARD] | exact SRC | exact BUFB | assumption
                   | subst nb; unfold zlength in *; lia]).
  Qed.
  End Sz13.
  Theorem stdio_write_spec : ltac:(let t := eval cbv delta [stdio_write_spec__stmt] in stdio_write_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn writefn seekfn B bufsize prev next mode lbf tail s S lo canary. ltac2:(SecDiet.SzSec.closeP 'stdio_write_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Entry.
End TwB.
End F_stdio_write.

(* [comment removed for export] *)
Module F_stdout_write.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition wfn_of (f : file_st) : Z := if f_stdoutw f then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (f : file_st) : Z := if f_lbf_nl f then 10 else 0xffffffff.
Definition WRITEFN_DEPTH : Z := 144.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs',
  rw_cells ssegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells ssegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
  intros a b E. cbn [cbytes]. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
  bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
  rw_cells ssegs m A (pre ++ C4 a :: post) -> rw_cells ssegs m A (pre ++ C4 b :: post).
Proof.
  intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac fix_lbf FC :=
  lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
    lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
      apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
               (Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
    end
  end.

(* [comment removed for export] *)
Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
  rw_cells ssegs m A (C4 v :: cs) -> rw_cells ssegs m A (CB 4 (le4 v) :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
  rw_cells ssegs m A (CB 4 (le4 v) :: cs) -> rw_cells ssegs m A (C4 v :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.
Lemma flags_byte_and64 : forall flags : word,
  Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
  intros flags H. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
  rewrite H. reflexivity.
Qed.

Section WriteFn.
  Context {St : Type}.

  Definition wf_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - WRITEFN_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  (* [comment removed for export] *)
  Definition f_after_write (f : file_st) : file_st := set_w true [] (if f_stdoutw f then after_ioctl f else f).

  Definition writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B bufsize prev next : Z) (mode : word) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => f' = f_after_write f /\ st' = st /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch (wf_W sp Fp) m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' Fp (fcells flags rpos rend closefn (B + bufsize) B B readfn F_STDIO_WRITE seekfn B bufsize prev next (f_fd f) mode (lbf_of (f_after_write f)) tail)
      /\ ssp_cells m' canary.

  Definition file_writefn_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn wend readfn seekfn B bufsize prev next : Z)
           (mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells ssegs m Fp (fcells flags rpos rend closefn wend (B + zlength (f_wbuf f)) B readfn (wfn_of f) seekfn B bufsize prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      bytes_at ssegs m B (to_bytes (f_wbuf f)) ->
      bytes_at ssegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31 /\ 1 <= zlength (f_wbuf f) + zlength s)) ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - WRITEFN_DEPTH -> 0x55000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv ssegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 <= B -> 0 <= bufsize -> B + bufsize < 2^64 -> B + zlength (f_wbuf f) <= 2^47 ->   (* [comment removed for export] *)
      0 <= S < 2^64 -> S + zlength s <= 2^47 (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S))) ->
      ((B + zlength (f_wbuf f) <= lo \/ bv_unsigned sp <= B) /\ (B + zlength (f_wbuf f) <= Fp \/ Fp + 232 <= B)) ->
      implM ssegs (file_writefn f s) st
        (writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B bufsize prev next mode tail (zlength s) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (wfn_of f)) fc None m (seg_rom ssegs)).
  Section Sz8.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn seekfn B bufsize prev next mode tail s S lo canary : ltac2:(SecDiet.SzSec.tyM 'file_writefn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma file_writefn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'file_writefn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FL64 BUFB SRC -> -> -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi BWB S0 Shi LENW SEPS SEPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, WRITEFN_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    assert (FD : 0 <= f_fd f < 2^31) by (destruct (f_chan f); lia).
    unfold file_writefn, wfn_of in *. unfold F_STDOUT_WRITE, F_STDIO_WRITE in *.
    destruct (f_stdoutw f) eqn:SW.
    - (* [comment removed for export] *)
      pose proof (munch_refl (wf_W sp Fp) m) as MU. pose proof (wmono_refl ssegs m) as WM. unfold wf_W, WRITEFN_DEPTH in MU.
      change (bytes_at ssegs m S (to_bytes s)) with (boxed (bytes_at ssegs m S (to_bytes s))) in SRC.
      change (bytes_at ssegs m B (to_bytes (f_wbuf f))) with (boxed (bytes_at ssegs m B (to_bytes (f_wbuf f)))) in BUFB.
      apply implM_sys_bind.
      unfold fcells, file_cells in FC. apply rw_cells_C4_CB4 in FC.
      carve_frame 32%nat ST.
      do 8 zs. rewrite firstn1_le4, zext_extract_le1. unfold zx8. do 5 zs.
      if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. apply Hsvb. change (2^8) with 256. apply flags_byte_and64. exact FL64. }
      do 7 zs. rewrite (sx32_small (f_fd f)) by lia. do 3 zs.
      step_ecall. split. { at_node_solve. }
      intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
      destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
      destruct Hdec as [-> He]. unfold efferr, eff0.
      (* [comment removed for export] *)
      apply implM_prefix. sys_nret.
      do 5 zs.
      if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
      zs. zs.
      fix_lbf FC.
      zs. apply evt_done.
      apply rw_cells_CB4_C4 in FC.
      eapply implM_post_evt.
      { eapply (stdio_write_spec (St:=St)) with (f := after_ioctl f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := wend) (readfn := readfn)
          (writefn := 0x1b3f4) (seekfn := seekfn) (B := B) (bufsize := bufsize) (prev := prev) (next := next) (mode := mode)
          (lbf := 4294967295) (tail := tail);
          cbn [f_wbuf f_fd f_chan after_ioctl]; rewrite ?unsigned_lit by lia.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold fcells, file_cells; exact FC]) | unfold boxed in BUFB; destruct SEPB as [SB1 SB2]; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia | unfold boxed in SRC; destruct SEPS as [-> | [SS1 SS2]]; [apply bytes_at_nil; lia|];
                     apply (bytes_at_transport _ _ _ _ _ _ SRC MU); cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_WRITE_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BShi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BWB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Shi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LENW]) | destruct SEPS as [-> | [SS1 SS2]]; [left; reflexivity | right; split; lia] | lia ]. }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & [GOT2 GUARD2]).
      unfold sw_W, STDIO_WRITE_DEPTH in MU2. unfold got_ssp, ssp_guard in GOT2, GUARD2. rewrite !unsigned_lit in MU2, ST2 by lia.
      (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 0x1bb8c)) with (Z_to_bv 64 0x1bb8c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rename x13 into m2.
      assert (FR2 : rw_cells ssegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
      { eapply (rw_cells_transport ssegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; lia]. }
      clear FR. step. step. step. if_false. step. step. step. step.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. unfold writefn_post, f_after_write, lbf_of. rewrite SW. cbn [f_lbf_nl after_ioctl set_w f_fd].
      split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { lazymatch type of MU with munch _ m ?mi => apply (munch_trans _ m mi m2) end.
        * eapply munch_weaken; [| exact MU]. unfold sub_fp, wf_W, WRITEFN_DEPTH in *; cbn [outside]; intros; lia.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, wf_W, WRITEFN_DEPTH in *; cbn [outside]; intros; lia. }
      split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
      split; [cbn [f_fd after_ioctl] in FC2; unfold F_STDIO_WRITE; exact FC2|]. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      eapply implM_post_evt.
      { eapply (stdio_write_spec (St:=St)) with (f := f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := wend) (readfn := readfn)
          (writefn := 0x1b3f4) (seekfn := seekfn) (B := B) (bufsize := bufsize) (prev := prev) (next := next) (mode := mode)
          (lbf := lbf_of f) (tail := tail).
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUFB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SRC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_WRITE_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SP47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SSP0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | unfold got_ssp, ssp_guard in *; lia | unfold got_ssp, ssp_guard in *; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BShi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BWB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Shi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LENW]) | destruct SEPS as [-> | [SS1 SS2]]; [left; reflexivity | right; split; lia] | lia ]. }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      apply evt_done. unfold writefn_post, f_after_write, lbf_of. rewrite SW.
      split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp, sw_W, wf_W, STDIO_WRITE_DEPTH, WRITEFN_DEPTH in *; cbn [outside]; intros; lia|].
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [unfold F_STDIO_WRITE; exact FC2 | exact SSP2].
  Qed.
  End Sz8.
  Theorem file_writefn_spec : ltac:(let t := eval cbv delta [file_writefn_spec__stmt] in file_writefn_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn seekfn B bufsize prev next mode tail s S lo canary. ltac2:(SecDiet.SzSec.closeP 'file_writefn_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End WriteFn.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition wfn_of (f : file_st) : Z := if f_stdoutw f then F_STDOUT_WRITE else F_STDIO_WRITE.
Definition lbf_of (f : file_st) : Z := if f_lbf_nl f then 10 else 0xffffffff.
Definition WRITEFN_DEPTH : Z := 144.   (* [comment removed for export] *)

(* [comment removed for export] *)
Lemma rw_cells_recast : forall m A cs cs',
  rw_cells usegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> cells_size cs' = cells_size cs ->
  rw_cells usegs m A cs'.
Proof. intros m A cs cs' [[Hwf Hb] Hw] Hwf' Eb Es. split; [split; [exact Hwf'| rewrite Eb; exact Hb] | rewrite Es; exact Hw]. Qed.
Lemma C4_low32 : forall (a b : word) , bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 -> cbytes (C4 a) = cbytes (C4 b).
Proof.
  intros a b E. cbn [cbytes]. unfold le4.
  rewrite <- (Z_to_le_bytes_mod 4 (bv_unsigned a) 32), <- (Z_to_le_bytes_mod 4 (bv_unsigned b) 32) by (cbn; lia).
  rewrite E. reflexivity.
Qed.
Lemma rw_cells_C4_eq : forall m A pre (a b : word) post,
  bv_unsigned a mod 2^32 = bv_unsigned b mod 2^32 ->
  rw_cells usegs m A (pre ++ C4 a :: post) -> rw_cells usegs m A (pre ++ C4 b :: post).
Proof.
  intros m A pre a b post E H. eapply rw_cells_recast; [exact H| | |].
  - destruct H as [[Hwf _] _]. apply cells_wf_app in Hwf. apply cells_wf_app. destruct Hwf as [H1 H2]. split; [exact H1|]. exact H2.
  - rewrite !cells_bytes_app. cbn [cells_bytes]. rewrite (C4_low32 a b E). reflexivity.
  - rewrite !cells_size_app. reflexivity.
Qed.
(* [comment removed for export] *)
Ltac fix_lbf FC :=
  lazymatch type of FC with rw_cells ?sg ?m' ?A ?cs =>
    lazymatch cs with ?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: ?c12 :: ?c13 :: ?c14 :: ?c15 :: ?c16 :: ?c17 :: ?c18 :: ?c19 :: ?c20 :: C4 (Z_to_bv 64 (-1)) :: ?rest =>
      apply (rw_cells_C4_eq m' A [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9; c10; c11; c12; c13; c14; c15; c16; c17; c18; c19; c20]
               (Z_to_bv 64 (-1)) (Z_to_bv 64 4294967295) rest ltac:(vm_compute; reflexivity)) in FC
    end
  end.

(* [comment removed for export] *)
Lemma rw_cells_C4_CB4 : forall m A (v : word) cs,
  rw_cells usegs m A (C4 v :: cs) -> rw_cells usegs m A (CB 4 (le4 v) :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [apply length_le4| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma rw_cells_CB4_C4 : forall m A (v : word) cs,
  rw_cells usegs m A (CB 4 (le4 v) :: cs) -> rw_cells usegs m A (C4 v :: cs).
Proof.
  intros m A v cs [[W B] R]. split; [split|].
  - cbn [cells_wf cell_wf] in *. split; [exact I| exact (proj2 W)].
  - exact B.
  - exact R.
Qed.
Lemma firstn1_le4 : forall v : word, firstn 1 (skipn 0 (le4 v)) = le1 v.
Proof. intros v. reflexivity. Qed.
Lemma flags_byte_and64 : forall flags : word,
  Z.land (bv_unsigned flags) 64 = 0 -> Z.land (bv_unsigned flags mod 256) 64 = 0.
Proof.
  intros flags H. change 256 with (2 ^ 8). rewrite <- Z.land_ones by lia.
  rewrite (Z.land_comm _ (Z.ones 8)), <- Z.land_assoc, (Z.land_comm (Z.ones 8)), Z.land_ones by lia.
  rewrite H. reflexivity.
Qed.

Section WriteFn.
  Context {St : Type}.

  Definition wf_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - WRITEFN_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  (* [comment removed for export] *)
  Definition f_after_write (f : file_st) : file_st := set_w true [] (if f_stdoutw f then after_ioctl f else f).

  Definition writefn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St)
      (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B bufsize prev next : Z) (mode : word) (tail : list byte)
      (len : Z) (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => f' = f_after_write f /\ st' = st /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 len) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch (wf_W sp Fp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' Fp (fcells flags rpos rend closefn (B + bufsize) B B readfn F_STDIO_WRITE seekfn B bufsize prev next (f_fd f) mode (lbf_of (f_after_write f)) tail)
      /\ ssp_cells m' canary.

  Definition file_writefn_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn wend readfn seekfn B bufsize prev next : Z)
           (mode : word) (tail : list byte) (s : list Z) (S lo : Z) (canary : word),
      rw_cells usegs m Fp (fcells flags rpos rend closefn wend (B + zlength (f_wbuf f)) B readfn (wfn_of f) seekfn B bufsize prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      bytes_at usegs m B (to_bytes (f_wbuf f)) ->
      bytes_at usegs m S (to_bytes s) ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 S -> a2 = Z_to_bv 64 (zlength s) ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31 /\ 1 <= zlength (f_wbuf f) + zlength s)) ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - WRITEFN_DEPTH -> 0x56000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv usegs m ->
      0 <= Fp -> (Fp + 232 <= lo \/ bv_unsigned sp <= Fp) ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 <= B -> 0 <= bufsize -> B + bufsize < 2^64 -> B + zlength (f_wbuf f) <= 2^47 ->   (* [comment removed for export] *)
      0 <= S < 2^64 -> S + zlength s <= 2^47 (* [comment removed for export] *) -> zlength (f_wbuf f) + zlength s <= 2^26 ->
      (s = [] \/ ((S + zlength s <= lo \/ bv_unsigned sp <= S) /\ (S + zlength s <= Fp \/ Fp + 232 <= S))) ->
      ((B + zlength (f_wbuf f) <= lo \/ bv_unsigned sp <= B) /\ (B + zlength (f_wbuf f) <= Fp \/ Fp + 232 <= B)) ->
      implM usegs (file_writefn f s) st
        (writefn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags rpos rend closefn readfn seekfn B bufsize prev next mode tail (zlength s) lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 (wfn_of f)) fc None m (seg_rom usegs)).
  Section Sz8.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn seekfn B bufsize prev next mode tail s S lo canary : ltac2:(SecDiet.SzSec.tyM 'file_writefn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma file_writefn_spec__body : ltac2:(SecDiet.SzSec.bodyP 'file_writefn_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros FC FL64 BUFB SRC -> -> -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BS0 BShi BWB S0 Shi LENW SEPS SEPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard, WRITEFN_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    assert (FD : 0 <= f_fd f < 2^31) by (destruct (f_chan f); lia).
    unfold file_writefn, wfn_of in *. unfold F_STDOUT_WRITE, F_STDIO_WRITE in *.
    destruct (f_stdoutw f) eqn:SW.
    - (* [comment removed for export] *)
      pose proof (munch_refl (wf_W sp Fp) m) as MU. pose proof (wmono_refl usegs m) as WM. unfold wf_W, WRITEFN_DEPTH in MU.
      change (bytes_at usegs m S (to_bytes s)) with (boxed (bytes_at usegs m S (to_bytes s))) in SRC.
      change (bytes_at usegs m B (to_bytes (f_wbuf f))) with (boxed (bytes_at usegs m B (to_bytes (f_wbuf f)))) in BUFB.
      apply implM_sys_bind.
      unfold fcells, file_cells in FC. apply rw_cells_C4_CB4 in FC.
      carve_frame 32%nat ST.
      do 8 zs. rewrite firstn1_le4, zext_extract_le1. unfold zx8. do 5 zs.
      if_cases Hsvb; zify_cond Hsvb. 1:{ exfalso. apply Hsvb. change (2^8) with 256. apply flags_byte_and64. exact FL64. }
      do 7 zs. rewrite (sx32_small (f_fd f)) by lia. do 3 zs.
      step_ecall. split. { at_node_solve. }
      intros rsp ans Hdec. unfold dec_ioctl in Hdec. apply dec_plain_Some in Hdec.
      destruct ans as [e|v]. 2:{ exfalso. destruct Hdec as (_ & Hok & _). discriminate Hok. }
      destruct Hdec as [-> He]. unfold efferr, eff0.
      (* [comment removed for export] *)
      apply implM_prefix. sys_nret.
      do 5 zs.
      if_cases He0; zify_cond He0. 1:{ exfalso. rewrite unsigned_errno_ret in He0 by lia. lia. }
      zs. zs.
      fix_lbf FC.
      zs. apply evt_done.
      apply rw_cells_CB4_C4 in FC.
      eapply implM_post_evt.
      { eapply (stdio_write_spec (St:=St)) with (f := after_ioctl f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := wend) (readfn := readfn)
          (writefn := 0x1bbb4) (seekfn := seekfn) (B := B) (bufsize := bufsize) (prev := prev) (next := next) (mode := mode)
          (lbf := 4294967295) (tail := tail);
          cbn [f_wbuf f_fd f_chan after_ioctl]; rewrite ?unsigned_lit by lia.
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold fcells, file_cells; exact FC]) | unfold boxed in BUFB; destruct SEPB as [SB1 SB2]; apply (bytes_at_transport _ _ _ _ _ _ BUFB MU); cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia | unfold boxed in SRC; destruct SEPS as [-> | [SS1 SS2]]; [apply bytes_at_nil; lia|];
                     apply (bytes_at_transport _ _ _ _ _ _ SRC MU); cbn [disjoint_from]; rewrite length_to_bytes; unfold zlength in *; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_WRITE_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [split; [exact GOT | exact GUARD]]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | lia | unfold got_ssp, ssp_guard; lia | unfold got_ssp, ssp_guard; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BShi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BWB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Shi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LENW]) | destruct SEPS as [-> | [SS1 SS2]]; [left; reflexivity | right; split; lia] | lia ]. }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & [GOT2 GUARD2]).
      unfold sw_W, STDIO_WRITE_DEPTH in MU2. unfold got_ssp, ssp_guard in GOT2, GUARD2. rewrite !unsigned_lit in MU2, ST2 by lia.
      (* [comment removed for export] *)
      replace (ret_pc (Z_to_bv 64 0x1c34c)) with (Z_to_bv 64 0x1c34c : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      rename x13 into m2.
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) [CB 8 (firstn 8 (firstn 16 (firstn 24 junk))); C8 canary; C8 s0; C8 ra]).
      { eapply (rw_cells_transport usegs _ _ m2); [exact FR | exact MU2 | exact WM2 | cbn; lia]. }
      clear FR. step. step. step. if_false. step. step. step. step.
      release_frame FR2 ST2 (bv_unsigned sp).
      apply evt_done. unfold writefn_post, f_after_write, lbf_of. rewrite SW. cbn [f_lbf_nl after_ioctl set_w f_fd].
      split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split.
      { lazymatch type of MU with munch _ m ?mi => apply (munch_trans _ m mi m2) end.
        * eapply munch_weaken; [| exact MU]. unfold sub_fp, wf_W, WRITEFN_DEPTH in *; cbn [outside]; intros; lia.
        * eapply munch_weaken; [| exact MU2]. unfold sub_fp, wf_W, WRITEFN_DEPTH in *; cbn [outside]; intros; lia. }
      split; [eapply wmono_trans; [exact WM | exact WM2]|]. split; [exact MI2|]. split; [exact ST2|].
      split; [cbn [f_fd after_ioctl] in FC2; unfold F_STDIO_WRITE; exact FC2|]. split; [exact GOT2 | exact GUARD2].
    - (* [comment removed for export] *)
      eapply implM_post_evt.
      { eapply (stdio_write_spec (St:=St)) with (f := f) (s := s) (S := S) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := wend) (readfn := readfn)
          (writefn := 0x1bbb4) (seekfn := seekfn) (B := B) (bufsize := bufsize) (prev := prev) (next := next) (mode := mode)
          (lbf := lbf_of f) (tail := tail).
        all: [> (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BUFB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SRC]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [reflexivity]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact CH]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact ST]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [unfold STDIO_WRITE_DEPTH; lia]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact GLO]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SP47]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact SSP0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact MI]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Fp0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact FPLO]) | unfold got_ssp, ssp_guard in *; lia | unfold got_ssp, ssp_guard in *; lia | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact B0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BS0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BShi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact BWB]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact S0]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact Shi]) | (let M := fresh "LIAFAST__" in pose proof LiaFastMode as M; solve [exact LENW]) | destruct SEPS as [-> | [SS1 SS2]]; [left; reflexivity | right; split; lia] | lia ]. }
      cbv beta. intros f' st' ms' (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      apply evt_done. unfold writefn_post, f_after_write, lbf_of. rewrite SW.
      split; [reflexivity|]. split; [reflexivity|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [eapply munch_weaken; [| exact MU2]; unfold sub_fp, sw_W, wf_W, STDIO_WRITE_DEPTH, WRITEFN_DEPTH in *; cbn [outside]; intros; lia|].
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [unfold F_STDIO_WRITE; exact FC2 | exact SSP2].
  Qed.
  End Sz8.
  Theorem file_writefn_spec : ltac:(let t := eval cbv delta [file_writefn_spec__stmt] in file_writefn_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn wend readfn seekfn B bufsize prev next mode tail s S lo canary. ltac2:(SecDiet.SzSec.closeP 'file_writefn_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End WriteFn.
End TwB.
End F_stdout_write.

(* [comment removed for export] *)
Module F_stdio_read.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys Require Import Uaccess.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_READ : Z := 0x1a8d4.
Definition STDIO_READ_DEPTH : Z := 80.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bv_eqb_eq' : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Definition dec_readv_Some2__stmt : Prop := forall d0 l0 d1 l1 rsp a,
  0 < l0 -> 0 < l1 -> 0 <= d0 -> 0 <= d1 ->
  dec_readv [(d0, l0); (d1, l1)] rsp = Some a ->
  match a with
  | RdErr e => rsp = efferr e /\ 1 <= e <= 4095
  | RdData bs =>
      let n := Z.of_nat (length bs) in
      n <= l0 + l1 /\
      rsp = mkEffect (Z_to_bv 64 n)
              (if n =? 0 then []
               else if n <=? l0 then [(Z_to_bv 64 d0, bs)]
               else [(Z_to_bv 64 d0, firstn (Z.to_nat l0) bs); (Z_to_bv 64 d1, skipn (Z.to_nat l0) bs)]) []
  end.
Section Sz2.
Variables d0 l0 d1 l1 : ltac2:(SecDiet.SzSec.tyM 'dec_readv_Some2__stmt "vvvv" @d0).
#[using="Type"] Lemma dec_readv_Some2__body : ltac2:(SecDiet.SzSec.bodyP 'dec_readv_Some2__stmt "vvvv").
Proof.
  intros [r ws zs us [|? ?] [|? ?]] a L0 L1 D0 D1 H; try discriminate H.
  unfold dec_readv in H. cbn [core] in H.
  destruct zs; [|discriminate H]. destruct us; [|discriminate H].
  destruct (errno_of r) as [e|] eqn:E.
  - destruct ws; [|discriminate H]. injection H as <-. apply errno_of_Some in E as [-> He]. split; [reflexivity| exact He].
  - unfold iovs_total_Z in H. cbn [fold_right snd fst] in H. rewrite Z.add_0_r in H.
    destruct (Z.leb_spec0 (bv_unsigned r) (l0 + l1)) as [LE|]; [|discriminate H].
    pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R. cbn in R.
    set (n := bv_unsigned r) in *.
    cbn [match_scatter] in H.
    destruct (Z.leb_spec0 (Z.min n l0) 0) as [Z0|P0].
    + assert (n = 0) by lia.
      destruct (Z.leb_spec0 (Z.min n l1) 0) as [_|P1]; [|exfalso; lia].
      destruct ws; [|discriminate H].
      replace (n =? 0) with true in H by (symmetry; apply Z.eqb_eq; lia). injection H as <-.
      cbn [length Z.of_nat Z.eqb]. split; [lia|]. f_equal. apply bv_eq. subst n. rewrite H0. reflexivity.
    + destruct ws as [|[x bs0] ws']; [discriminate H|].
      destruct (bv_eqb x (Z_to_bv 64 d0)) eqn:EX; [|discriminate H]. apply bv_eqb_eq' in EX. subst x.
      destruct (Z.eqb_spec (Z.of_nat (length bs0)) (Z.min n l0)) as [EL|]; [|discriminate H]. cbn [andb] in H.
      destruct (Z.leb_spec0 (Z.min (n - Z.min n l0) l1) 0) as [Z1|P1].
      * destruct ws'; [|discriminate H].
        destruct (Z.eqb_spec (n - Z.min n l0) 0) as [E0|]; [|discriminate H]. injection H as <-.
        rewrite app_nil_r. cbn zeta. assert (EN : Z.of_nat (length bs0) = n) by lia.
        split; [lia|]. rewrite EN.
        replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (n <=? l0) with true by (symmetry; apply Z.leb_le; lia).
        f_equal. apply bv_eq. rewrite unsigned_lit by lia. reflexivity.
      * destruct ws' as [|[y bs1] ws'']; [discriminate H|].
        destruct (bv_eqb y (Z_to_bv 64 d1)) eqn:EY; [|discriminate H]. apply bv_eqb_eq' in EY. subst y.
        destruct (Z.eqb_spec (Z.of_nat (length bs1)) (Z.min (n - Z.min n l0) l1)) as [EL1|]; [|discriminate H]. cbn [andb] in H.
        destruct ws''; [|discriminate H].
        destruct (Z.eqb_spec (n - Z.min n l0 - Z.min (n - Z.min n l0) l1) 0) as [E0|]; [|discriminate H]. injection H as <-.
        rewrite app_nil_r. cbn zeta. rewrite length_app.
        assert (EN : Z.of_nat (length bs0 + length bs1) = n) by lia.
        split; [lia|]. rewrite EN.
        replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (n <=? l0) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.to_nat l0) with (length bs0) by lia.
        rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all, skipn_app, Nat.sub_diag, skipn_O, skipn_all, app_nil_l.
        f_equal. apply bv_eq. rewrite unsigned_lit by lia. reflexivity.
Qed.
End Sz2.
Lemma dec_readv_Some2 : ltac:(let t := eval cbv delta [dec_readv_Some2__stmt] in dec_readv_Some2__stmt in exact t).
Proof. intros d0 l0 d1 l1. ltac2:(SecDiet.SzSec.closeP 'dec_readv_Some2__body "vvvv"). Qed.

Lemma to_of_bytes : forall l, to_bytes (of_bytes l) = l.
Proof. intros l. unfold to_bytes, of_bytes. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma FR_map : forall l : list byte, Forall (fun z => 0 <= z < 256) (map bv_unsigned l).
Proof. induction l as [|b l IH]; constructor; [pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia| exact IH]. Qed.
Lemma FR_cons : forall (b : byte) l, Forall (fun z => 0 <= z < 256) l -> Forall (fun z => 0 <= z < 256) (bv_unsigned b :: l).
Proof. intros b l H. constructor; [pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia| exact H]. Qed.
Lemma FR_app : forall a b : list Z, Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) b -> Forall (fun z => 0 <= z < 256) (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. split; assumption. Qed.
Lemma FR_firstn : forall k (a : list Z), Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) (firstn k a).
Proof. intros k a H. rewrite <- (firstn_skipn k a) in H. apply Forall_app in H. destruct H as [H _]. exact H. Qed.
Lemma FR_skipn : forall k (a : list Z), Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) (skipn k a).
Proof. intros k a H. rewrite <- (firstn_skipn k a) in H. apply Forall_app in H. destruct H as [_ H]. exact H. Qed.
Ltac frange :=
  repeat first [ assumption | apply Forall_nil | apply FR_map | apply FR_cons | apply FR_app | apply FR_firstn | apply FR_skipn
               | match goal with H : f_rbuf ?f = [] |- Forall _ (f_rbuf ?f) => rewrite H end
               | progress cbn [fst snd f_rbuf set_rbuf set_eof set_w of_bytes] ].
Lemma length_of_bytes : forall l, length (of_bytes l) = length l.
Proof. intros. unfold of_bytes. apply length_map. Qed.

(* [comment removed for export] *)
Lemma apply_mem_write2 : forall m a1 b1 a2 b2,
  apply_writes (apply_zeros (apply_unmaps m []) []) [(a1, b1); (a2, b2)] = write_to_mem (write_to_mem m a1 b1) a2 b2.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac sys_mem_write_inner :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?a2 ?bs2) ?ro) =>
    change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
    lazymatch goal with
    | H : rw_cells segs m B [CB ?n ?junk] |- _ =>
        let HB := fresh "HB" in
        pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
        (try lazymatch goal with
         | HI : mem_inv segs m |- _ =>
             let HI' := fresh "MI" in
             pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
         end);
        let H' := fresh "DST" in
        pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
        clear H;
        transport_chunks segs m B bs;
        footprint_after_store segs m B bs;
        let m' := fresh "m" in
        remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
        clear Heqm; clear HB; try clear m; rename H' into H
    | _ => fail "sys_mem_write_inner: no hypothesis rw_cells" segs m B "[CB _ _]"
    end
  end.

(* [comment removed for export] *)
Definition iov_bytes0__stmt : Prop := forall m A (w0 w1 w2 w3 : word) rest,
  rw_cells ssegs m A (C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: rest) ->
  bytes_at ssegs m A (iovec_bytes [(w0, w1); (w2, w3)]).
Section Sz11.
Variables m A w0 w1 w2 w3 rest : ltac2:(SecDiet.SzSec.tyM 'iov_bytes0__stmt "vvvvvvv" @m).
#[using="Type"] Lemma iov_bytes0__body : ltac2:(SecDiet.SzSec.bodyP 'iov_bytes0__stmt "vvvvvvv").
Proof.
  intros FR.
  destruct FR as [[WF FB] _]. cbn [cells_bytes cbytes] in FB.
  apply bytes_at_app in FB as [FB0 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB3 _].
  cbn [iovec_bytes flat_map fst snd]. rewrite !app_nil_r.
  apply bytes_at_app. rewrite length_app, !length_le8. split.
  - apply bytes_at_app. rewrite length_le8. split; [exact FB0 | exact FB1].
  - apply bytes_at_app. rewrite length_le8. split.
    + replace (A + Z.of_nat (8 + 8)) with (A + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
    + replace (A + Z.of_nat (8 + 8) + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
Qed.
End Sz11.
Lemma iov_bytes0 : ltac:(let t := eval cbv delta [iov_bytes0__stmt] in iov_bytes0__stmt in exact t).
Proof. intros m A w0 w1 w2 w3 rest. ltac2:(SecDiet.SzSec.closeP 'iov_bytes0__body "vvvvvvv"). Qed.

(* [comment removed for export] *)
Definition flags_ok (f : file_st) (flags : word) : Prop :=
  Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0)
  /\ Z.land (bv_unsigned flags) F_NOWR = (if f_nowr f then F_NOWR else 0)
  /\ Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0)
  /\ Z.land (bv_unsigned flags) F_ERR = 0
  /\ Z.land (bv_unsigned flags) F_SVB = 0
  /\ Z.land (bv_unsigned flags) F_PERM = (if f_chan f then F_PERM else 0).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition land_mod32__stmt : Prop := forall a k, 0 <= k < 2^32 -> 0 <= a -> Z.land (a mod 2^32) k = Z.land a k.
Section Sz12.
Variables a k : ltac2:(SecDiet.SzSec.tyM 'land_mod32__stmt "vv" @a).
#[using="Type"] Lemma land_mod32__body : ltac2:(SecDiet.SzSec.bodyP 'land_mod32__stmt "vv").
Proof.
  intros Hk Ha.
 apply Z.bits_inj'; intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 32) as [L|G].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit k i) with false; [rewrite !andb_false_r; reflexivity|].
    symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
    eapply Z.lt_le_trans; [apply (proj2 Hk)|]. apply Z.pow_le_mono_r; lia.
Qed.
End Sz12.
Lemma land_mod32 : ltac:(let t := eval cbv delta [land_mod32__stmt] in land_mod32__stmt in exact t).
Proof. intros a k. ltac2:(SecDiet.SzSec.closeP 'land_mod32__body "vv"). Qed.
Lemma sx32_mod32 : forall w : word, bv_unsigned (sx32 w) mod 2^32 = bv_unsigned w mod 2^32.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. nia.
Qed.
Lemma lor16_mod32 : forall a, 0 <= a -> Z.lor a 16 mod 2^32 = Z.lor (a mod 2^32) 16.
Proof.
  intros a Ha. rewrite <- !Z.land_ones by lia. rewrite Z.land_lor_distr_l. f_equal.
Qed.
Definition flags_ok_eof__stmt : Prop := forall f (flags : word), flags_ok f flags -> flags_ok (set_eof f) (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)).
Section Sz15.
Variables f flags : ltac2:(SecDiet.SzSec.tyM 'flags_ok_eof__stmt "vv" @f).
#[using="Type"] Lemma flags_ok_eof__body : ltac2:(SecDiet.SzSec.bodyP 'flags_ok_eof__stmt "vv").
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6).
 unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *. cbn [f_nord f_nowr f_eof f_chan set_eof].
  pose proof (bv_unsigned_in_range 64 flags) as R. unfold bv_modulus in R.
  rewrite unsigned_lit by (pose proof (Z_lor_range (bv_unsigned flags) 16 ltac:(lia) ltac:(lia)); lia).
  rewrite !Z.land_lor_distr_l. rewrite H1, H2, H4, H5, H6.
  change (Z.land 16 4) with 0. change (Z.land 16 8) with 0. change (Z.land 16 16) with 16. change (Z.land 16 32) with 0. change (Z.land 16 64) with 0. change (Z.land 16 1) with 0.
  rewrite !Z.lor_0_r. repeat split; try reflexivity.
  rewrite H3. destruct (f_eof f); reflexivity.
Qed.
End Sz15.
Lemma flags_ok_eof : ltac:(let t := eval cbv delta [flags_ok_eof__stmt] in flags_ok_eof__stmt in exact t).
Proof. intros f flags. ltac2:(SecDiet.SzSec.closeP 'flags_ok_eof__body "vv"). Qed.

Lemma rw_cells_CB0 : forall m A cs, rw_cells ssegs m A cs -> rw_cells ssegs m A (CB 0 [] :: cs).
Proof.
  intros m A cs [[W B] R]. split; [split|].
  - cbn. split; [reflexivity | exact W].
  - cbn [cells_bytes cbytes app]. exact B.
  - cbn [cells_size csize]. exact R.
Qed.
Lemma flags_cell_eof : forall m A (flags : word) rest,
  rw_cells ssegs m A (C4 (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags)) 16)) :: rest) ->
  rw_cells ssegs m A (C4 (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)) :: rest).
Proof.
  intros m A flags rest H. apply (rw_cells_C4_eq m A [] (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags)) 16)) (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)) rest); [|exact H].
  pose proof (bv_unsigned_in_range 64 flags) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2. unfold bv_modulus in R1, R2.
  cbn in R1, R2. pose proof (Z_lor_range (bv_unsigned (sx32 flags)) 16 ltac:(lia) ltac:(lia)). pose proof (Z_lor_range (bv_unsigned flags) 16 ltac:(lia) ltac:(lia)).
  rewrite !unsigned_lit by lia.
  rewrite !lor16_mod32 by lia. rewrite sx32_mod32. reflexivity.
Qed.

Section StdioRead.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition rd_inv (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_stdoutw f' = f_stdoutw f /\ f_lbf_nl f' = f_lbf_nl f
    /\ (f_eof f = true -> f_eof f' = true).

  Definition rd_W (sp : word) (Fp B bs D len : Z) : list (Z * Z) :=
    [(bv_unsigned sp - STDIO_READ_DEPTH, bv_unsigned sp); (Fp, Fp + 232); (B, B + bs); (D, D + len)].

  Definition stdio_read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (closefn readfn seekfn B prev next : Z) (mode : word) (tail : list byte)
      (D len : Z) (djunk : list byte) (lo : Z) (canary : word) (m : mem) : (list Z * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ rd_inv f (snd r) /\ Z.of_nat (length (fst r)) <= len /\
      (Z.of_nat (length (fst r)) < len -> f_rbuf (snd r) = []) /\
      Forall (fun z => 0 <= z < 256) (fst r) /\ Forall (fun z => 0 <= z < 256) (f_rbuf (snd r)) /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' : word) (rp' : Z) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch (rd_W sp Fp B (f_bufsize f) D len) m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' Fp (fcells flags' rp' (rp' + zlength (f_rbuf (snd r))) closefn 0 0 0 readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)
      /\ flags_ok (snd r) flags'
      /\ rw_cells ssegs m' B [CB (Z.to_nat (f_bufsize f)) bufbytes']
      /\ (f_rbuf (snd r) <> [] -> B <= rp' /\ rp' + zlength (f_rbuf (snd r)) <= B + f_bufsize f
                                /\ firstn (length (f_rbuf (snd r))) (skipn (Z.to_nat (rp' - B)) bufbytes') = to_bytes (f_rbuf (snd r)))
      /\ 0 <= rp' /\ rp' + zlength (f_rbuf (snd r)) < 2^63
      /\ rw_cells ssegs m' D [CB (length (fst r)) (to_bytes (fst r)); CB (Z.to_nat len - length (fst r)) (skipn (length (fst r)) djunk)]
      /\ ssp_cells m' canary.

  Definition stdio_read_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rp closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (D len : Z) (djunk : list byte) (lo : Z) (canary : word),
      rw_cells ssegs m Fp (fcells flags rp rp closefn 0 0 0 readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      flags_ok f flags -> 0 <= rp < 2^63 ->
      rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] ->
      rw_cells ssegs m D [CB (Z.to_nat len) djunk] ->
      f_wactive f = false -> f_wbuf f = [] -> f_rbuf f = [] -> f_chan f = false -> 3 <= f_fd f < 2^31 ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 len ->
      1 <= len -> 0 < f_bufsize f <= 2^20 -> len <= 2^30 ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STDIO_READ_DEPTH -> 0x55000 <= lo -> bv_unsigned sp <= 2^47 ->
      ssp_cells m canary -> mem_inv ssegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      (D + len <= got_ssp \/ got_ssp + 8 <= D) -> (D + len <= ssp_guard \/ ssp_guard + 8 <= D) ->
      0 < B -> B + f_bufsize f <= 2^47 -> 0 <= D -> D + len <= 2^47 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) -> (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      (D + len <= lo \/ bv_unsigned sp <= D) -> (D + len <= Fp \/ Fp + 232 <= D) -> (D + len <= B \/ B + f_bufsize f <= D) ->
      implM ssegs (stdio_read f B D len) st
        (stdio_read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp closefn readfn seekfn B prev next mode tail D len djunk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_READ) fc None m (seg_rom ssegs)).
  Section Sz18.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn seekfn B prev next mode tail bufbytes D len djunk lo canary : ltac2:(SecDiet.SzSec.tyM 'stdio_read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma stdio_read_spec__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FL RPR BUF DST WACT WB0 RB0 NCH FD -> -> -> L1 BS LMAX ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D0 D47 SB1 SB2 SD1 SD2 SD3.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold STDIO_READ, STDIO_READ_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (rd_W sp Fp B (f_bufsize f) D len) m) as MU. pose proof (wmono_refl ssegs m) as WM. unfold rd_W, STDIO_READ_DEPTH in MU.
    unfold fcells, file_cells in FC.
    unfold stdio_read.
    replace (f_bufsize f =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn zeta.
    apply implM_prefix.
    carve_frame 80%nat ST.
    do 13 zs. do 3 zs. rewrite (sx32_small (f_fd f)) by lia.
    do 6 zs.
    assert (HB1 : (0 <? f_bufsize f) = true) by (apply Z.ltb_lt; lia). rewrite HB1 in *. cbn [Z.b2z] in *.
    destruct (Z.eq_dec len 1) as [L1eq | Lgt].
    - (* [comment removed for export] *)
      subst len. change (1 - 1 =? 0) with true. cbv iota. change (1 - 1) with 0 in *.
      zs. if_true. zs.
      apply evt_done. apply implM_sys_bind.
      step_ecall. split.
      { at_node_red; split_spine; try reflexivity; try lia.
        - unfold max_read. lia.   (* [comment removed for export] *)
        - apply (rw_cells_wr_at ssegs _ _ _ _ BUF). cbn [cells_size csize]. lia. }
      intros rsp ans Hdec.
      apply (dec_read_Some B (f_bufsize f)) in Hdec; [| lia].
      destruct ans as [e | raw].
      { apply implM_unr. }
      destruct Hdec as [-> NLE].
      unfold zlength. rewrite length_of_bytes.
      destruct raw as [|b0 rest2].
      + (* [comment removed for export] *)
        cbn [length Z.of_nat Z.eqb delivered_writes].
        apply implM_prefix. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x1a990)) with (Z_to_bv 64 0x1a990 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. lia. }
        zs. if_true. zs. zs. zs. zs. zs.
        do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. apply implM_ret. apply evt_done.
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        apply flags_cell_eof in FC.
        unfold stdio_read_post. cbn [fst snd f_rbuf set_eof length of_bytes map].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)), rp, bufbytes, mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        split; [unfold fcells, file_cells; exact FC|]. split; [apply flags_ok_eof; exact FL|].
        split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
        split; [apply rw_cells_CB0; exact DST|]. split; [exact GOT | exact GUARD].
      + (* [comment removed for export] *)
        cbn [delivered_writes].
        set (raw' := b0 :: rest2) in *. assert (ER : raw' = b0 :: rest2) by reflexivity. assert (LRW : length raw' = S (length rest2)) by reflexivity.
        clearbody raw'. cbn [length] in NLE.
        replace (Z.of_nat (length raw') =? 0) with false by (rewrite LRW; reflexivity).
        replace (Z.of_nat (length raw') <=? 0) with false by (rewrite LRW; reflexivity).
        apply implM_prefix. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x1a990)) with (Z_to_bv 64 0x1a990 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. if_cases Hp; zify_cond Hp. 2:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
        zs. zs. if_cases Hq; zify_cond Hq. 1:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
        zs. zs. zs. zs. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
        zs. zs.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
        assert (HR : ov_read_bytes ssegs mC (wa (B + 0)) 1 = Some [b0]).
        { pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BB. cbn [cells_bytes cbytes] in BB. rewrite ER in BB.
          rewrite (bytes_at_read ssegs mC B _ 0 1 BB); [reflexivity | lia | cbn; rewrite length_app; cbn; lia]. }
        zs. zs.
        assert (HS : store_ok ssegs mC (wa (D + 0)) 1 = true).
        { apply (wr_at_store_ok ssegs mC D 1 0 1); [| lia | lia].
          apply (rw_cells_wr_at ssegs _ _ _ _ DST). cbn [cells_size csize]. lia. }
        zs.
        change (Z_to_bv 64 (bv_unsigned b0)) with (zxb b0). rewrite le1_zxb.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?a _) _) =>
          replace a with (wa D) by (unfold wa; f_equal; lia) end.
        pose proof (rw_cells_CB_prefix_write ssegs mC D _ _ [b0] DST ltac:(cbn; lia)) as DST2. cbn [length] in DST2.
        store_done.
        zs. do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. apply implM_ret. apply evt_done.
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        subst raw'. cbn [length] in LRW, NLE.
        pose proof (rw_cells_merge ssegs mZ B [] [CB (length (b0 :: rest2)) (b0 :: rest2); CB (Z.to_nat (f_bufsize f) - length (b0 :: rest2)) (skipn (length (b0 :: rest2)) bufbytes)] []) as BM.
        cbn [app] in BM. specialize (BM BUF). cbn [cells_size cells_bytes csize cbytes app Nat.add] in BM. rewrite app_nil_r in BM.
        replace (length (b0 :: rest2) + (Z.to_nat (f_bufsize f) - length (b0 :: rest2) + 0))%nat with (Z.to_nat (f_bufsize f)) in BM by (cbn [length] in NLE |- *; lia).
        unfold stdio_read_post. cbn [fst snd]. replace (Z.to_nat 0) with 0%nat by reflexivity. cbn [of_bytes map f_rbuf set_rbuf]. rewrite !skipn_O, !firstn_O.
        repeat match goal with |- context [skipn 1 (?a :: ?l)] => change (skipn 1 (a :: l)) with l end.
        repeat match goal with |- context [firstn 1 (?a :: ?l)] => change (firstn 1 (a :: l)) with [a] end.
        cbn [app length].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros HH; exfalso; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists flags, (B + 1), ((b0 :: rest2) ++ skipn (length (b0 :: rest2)) bufbytes), mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        unfold zlength. rewrite ?length_map.
        split. { unfold fcells, file_cells. replace (B + 1 + Z.of_nat (length rest2)) with (B + (Z.of_nat (length (b0 :: rest2)) - 0)) by (cbn [length]; lia). exact FC. }
        split; [exact FL|].
        split; [exact BM|].
        split. { intros _. rewrite ?length_map. split; [lia|]. split; [lia|]. replace (Z.to_nat (B + 1 - B)) with 1%nat by lia. rewrite <- app_comm_cons.
                 repeat match goal with |- context [skipn 1 (?a :: ?l)] => change (skipn 1 (a :: l)) with l end.
                 rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r. fold (of_bytes rest2). rewrite to_of_bytes. apply firstn_all2. lia. }
        split; [lia|]. split; [lia|].
        split. { cbn [length Nat.sub]. change (to_bytes [bv_unsigned b0]) with (to_bytes (of_bytes [b0])). rewrite to_of_bytes. exact DST2. }
        split; [exact GOT | exact GUARD].
    - (* [comment removed for export] *)
      replace (len - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs.
      apply evt_done. apply implM_sys_bind.
      step_ecall. split.
      { lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells ssegs mm (bv_unsigned sp + -80) _ |- _ =>
            pose proof (iov_bytes0 _ _ _ _ _ _ _ FRM) as IOV end end.
        at_node_red; split_spine.
        - reflexivity.
        - lia.
        - reflexivity.
        - reflexivity.
        - cbn; lia.
        - rewrite unsigned_lit by lia. cbn [length Z.of_nat]. lia.
        - lia.
        - cbn [dsts_total]. unfold MAX_RW_COUNT. lia.
        - constructor; [|constructor; [|constructor]]; cbn [fst snd].
          + split; [lia|]. split; [lia|].
            apply (rw_cells_wr_at ssegs _ _ _ _ DST). cbn [cells_size csize]. lia.
          + split; [lia|]. split; [lia|].
            apply (rw_cells_wr_at ssegs _ _ _ _ BUF). cbn [cells_size csize]. lia.
        - reflexivity.
        - rewrite unsigned_lit by lia. cbn [iovs_of map fst snd]. exact IOV. }
      intros rsp ans Hdec.
      apply (dec_readv_Some2 D (len - 1) B (f_bufsize f)) in Hdec; [| lia | lia | lia | lia].
      destruct ans as [e | raw].
      { (* [comment removed for export] *) apply implM_unr. }
      cbv zeta in Hdec. destruct Hdec as [NLE ->].
      set (n := Z.of_nat (length raw)) in *.
      unfold zlength. rewrite length_of_bytes. fold n.
      destruct (Z.eqb_spec n 0) as [N0 | N0].
      + (* [comment removed for export] *)
        replace (n =? 0) with true by (symmetry; apply Z.eqb_eq; exact N0).
        apply implM_prefix. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x1a944)) with (Z_to_bv 64 0x1a944 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        rewrite N0. zs. if_true. zs. if_true. zs. zs. zs. zs. zs.
        (* [comment removed for export] *)
        do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. apply implM_ret. apply evt_done.
        assert (raw = []) as -> by (destruct raw; [reflexivity | exfalso; subst n; cbn in N0; lia]).
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        apply flags_cell_eof in FC.
        unfold stdio_read_post. cbn [fst snd f_rbuf set_eof length of_bytes map].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)), rp, bufbytes, mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r, Nat.sub_0_r.
        split; [unfold fcells, file_cells; exact FC|]. split; [apply flags_ok_eof; exact FL|].
        split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
        split; [apply rw_cells_CB0; exact DST|]. split; [exact GOT | exact GUARD].
      + replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact N0).
        destruct (Z.leb_spec0 n (len - 1)) as [LE1 | GT1].
        * (* [comment removed for export] *)
          replace (n <=? len - 1) with true by (symmetry; apply Z.leb_le; exact LE1).
          apply implM_prefix. sys_nret.
          step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
          step.
          replace (ret_pc (Z_to_bv 64 0x1a944)) with (Z_to_bv 64 0x1a944 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
          zs. zs. if_cases Hq; zify_cond Hq. 2:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
          zs. zs.
          do 3 zs. if_false. do 8 zs.
          release_frame FR ST (bv_unsigned sp).
          apply evt_done. apply implM_ret. apply evt_done.
          lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
          unfold stdio_read_post. cbn [fst snd].
          split; [reflexivity|]. split; [unfold rd_inv; repeat split; auto|]. split; [rewrite length_of_bytes; lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
          do 14 eexists. exists flags, rp, bufbytes, mZ.
          split; [cbv delta [mkR]; unfold zlength; rewrite length_of_bytes; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
          split; [unfold fcells, file_cells; exact FC|]. split; [exact FL|].
          split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
          split; [rewrite to_of_bytes, length_of_bytes; exact DST|]. split; [exact GOT | exact GUARD].
        * (* [comment removed for export] *)
          replace (n <=? len - 1) with false by (symmetry; apply Z.leb_gt; lia).
          apply implM_prefix.
          rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs.
          lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
              let p' := eval vm_compute in (p + 4)%Z in
              replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
          end.
          rewrite apply_mem_write2.
          assert (LF : length (firstn (Z.to_nat (len - 1)) raw) = Z.to_nat (len - 1)) by (rewrite length_firstn; lia).
          assert (LS : length (skipn (Z.to_nat (len - 1)) raw) = (length raw - Z.to_nat (len - 1))%nat) by (rewrite length_skipn; lia).
          sys_mem_write_inner.
          sys_mem_write.
          rewrite LF in DST. rewrite LS in BUF.
          assert (exists b0 rest2, skipn (Z.to_nat (len - 1)) raw = b0 :: rest2) as (b0 & rest2 & EB2).
          { destruct (skipn (Z.to_nat (len - 1)) raw) as [|b0 r2] eqn:E; [exfalso; cbn in LS; lia | exists b0, r2; reflexivity]. }
          rewrite EB2 in BUF. cbn [length] in BUF.
          step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
          step.
          replace (ret_pc (Z_to_bv 64 0x1a944)) with (Z_to_bv 64 0x1a944 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
          zs. zs. if_cases Hq; zify_cond Hq. 1:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
          zs. zs. zs. zs. zs. zs.
          zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
          zs. zs.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
          assert (HR : ov_read_bytes ssegs mC (wa (B + 0)) 1 = Some [b0]).
          { pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BB. cbn [cells_bytes cbytes] in BB.
            rewrite (bytes_at_read ssegs mC B _ 0 1 BB); [reflexivity | lia | cbn; rewrite length_app; cbn; lia]. }
          zs. zs.
          assert (HS : store_ok ssegs mC (wa (D + (len - 1))) 1 = true).
          { apply (wr_at_store_ok ssegs mC D len (len - 1) 1); [| lia | lia].
            apply (rw_cells_wr_at ssegs _ _ _ _ DST). cbn [cells_size csize]. lia. }
          zs.
          change (Z_to_bv 64 (bv_unsigned b0)) with (zxb b0). rewrite le1_zxb.
          (* [comment removed for export] *)
          set (k := Z.to_nat (len - 1)) in *.
          pose proof DST as DST0.
          apply (proj1 (rw_cells_app ssegs _ _ [_] [_])) in DST0. destruct DST0 as [DSTa DSTb].
          cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
          assert (DST2 : rw_cells ssegs (write_to_mem mC (wa (D + (len - 1))) [b0]) D
                           [CB (k + 1) (firstn k raw ++ [b0]); CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))]).
          { replace (D + (len - 1)) with (D + Z.of_nat k) by lia.
            assert (A1 : rw_cells ssegs (write_to_mem mC (wa (D + Z.of_nat k)) [b0]) D [CB k (firstn k raw)]).
            { apply rw_cells_frame; [exact DSTa | lia | cbn; lia | cbn [cells_size csize length]; lia]. }
            pose proof (rw_cells_CB_prefix_write ssegs mC (D + Z.of_nat k) _ _ [b0] DSTb ltac:(cbn; lia)) as A2. cbn [length] in A2.
            pose proof (proj2 (rw_cells_app ssegs (write_to_mem mC (wa (D + Z.of_nat k)) [b0]) D [CB k (firstn k raw)] [CB 1 [b0]; CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))])) as J.
            cbn [cells_size csize Nat.add app] in J. rewrite ?Nat.add_0_r in J. specialize (J (conj A1 A2)).
            apply (rw_cells_merge ssegs _ D [] [CB k (firstn k raw); CB 1 [b0]] [CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))]) in J.
            cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite ?Nat.add_0_r, ?app_nil_r in J. exact J. }
          clear DSTa DSTb.
          store_done.
          zs. do 3 zs. if_false. do 8 zs.
          release_frame FR ST (bv_unsigned sp).
          apply evt_done. apply implM_ret. apply evt_done.
          lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
          (* [comment removed for export] *)
          pose proof (rw_cells_merge ssegs mZ B [] [CB (length raw - k) (b0 :: rest2); CB (Z.to_nat (f_bufsize f) - (length raw - k)) (skipn (length raw - k) bufbytes)] []) as BM.
          cbn [app] in BM. specialize (BM BUF). cbn [cells_size cells_bytes csize cbytes app Nat.add] in BM. rewrite app_nil_r in BM.
          replace (length raw - k + (Z.to_nat (f_bufsize f) - (length raw - k) + 0))%nat with (Z.to_nat (f_bufsize f)) in BM by lia.
          assert (RB : skipn 1 (skipn k (of_bytes raw)) = of_bytes rest2).
          { unfold of_bytes. rewrite !skipn_map, EB2. reflexivity. }
          assert (HD : firstn k (of_bytes raw) ++ firstn 1 (skipn k (of_bytes raw)) = of_bytes (firstn k raw ++ [b0])).
          { unfold of_bytes. rewrite firstn_map, skipn_map, EB2, map_app. reflexivity. }
          assert (LR2 : Z.of_nat (length rest2) = n - len).
          { apply (f_equal (@length byte)) in EB2. rewrite length_skipn in EB2. cbn [length] in EB2. lia. }
          unfold stdio_read_post. cbn [fst snd]. rewrite RB, HD. cbn [f_rbuf set_rbuf].
          split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|].
          split; [rewrite length_of_bytes, length_app; cbn [length]; lia|].
          split; [rewrite length_of_bytes, length_app; cbn [length]; intros HH; exfalso; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
          do 14 eexists. exists flags, (B + 1), ((b0 :: rest2) ++ skipn (length raw - k) bufbytes), mZ.
          split; [cbv delta [mkR]; unfold zlength; rewrite length_of_bytes, length_app; cbn [length]; repeat f_equal; lia|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          unfold zlength. rewrite !length_of_bytes.
          split. { unfold fcells, file_cells. replace (B + 1 + Z.of_nat (length rest2)) with (B + (n - (len - 1))) by lia. exact FC. }
          split; [exact FL|].
          split; [exact BM|].
          split. { intros _. split; [lia|]. split; [lia|]. replace (Z.to_nat (B + 1 - B)) with 1%nat by lia. rewrite <- app_comm_cons. cbn [skipn].
                   rewrite ?skipn_O, ?length_of_bytes, firstn_app, Nat.sub_diag, firstn_O, app_nil_r, to_of_bytes. apply firstn_all2. lia. }
          split; [lia|]. split; [lia|].
          split. { rewrite to_of_bytes, length_app, length_firstn. cbn [length].
                   replace (Nat.min k (length raw) + 1)%nat with (k + 1)%nat by lia.
                   rewrite skipn_skipn in DST2. replace (1 + k)%nat with (k + 1)%nat in DST2 by lia.
                   replace (Z.to_nat len - (k + 1))%nat with (Z.to_nat len - k - 1)%nat by lia. exact DST2. }
          split; [exact GOT | exact GUARD].
  Qed.
  End Sz18.
  Theorem stdio_read_spec : ltac:(let t := eval cbv delta [stdio_read_spec__stmt] in stdio_read_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn seekfn B prev next mode tail bufbytes D len djunk lo canary. ltac2:(SecDiet.SzSec.closeP 'stdio_read_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End StdioRead.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.LinuxProcessSem.Sys.Uaccess.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition STDIO_READ : Z := 0x1b094.
Definition STDIO_READ_DEPTH : Z := 80.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bv_eqb_eq' : forall {n} (a b : bv n), bv_eqb a b = true -> a = b.
Proof. intros n a b H. unfold bv_eqb in H. apply Z.eqb_eq in H. apply bv_eq. exact H. Qed.

Definition dec_readv_Some2__stmt : Prop := forall d0 l0 d1 l1 rsp a,
  0 < l0 -> 0 < l1 -> 0 <= d0 -> 0 <= d1 ->
  dec_readv [(d0, l0); (d1, l1)] rsp = Some a ->
  match a with
  | RdErr e => rsp = efferr e /\ 1 <= e <= 4095
  | RdData bs =>
      let n := Z.of_nat (length bs) in
      n <= l0 + l1 /\
      rsp = mkEffect (Z_to_bv 64 n)
              (if n =? 0 then []
               else if n <=? l0 then [(Z_to_bv 64 d0, bs)]
               else [(Z_to_bv 64 d0, firstn (Z.to_nat l0) bs); (Z_to_bv 64 d1, skipn (Z.to_nat l0) bs)]) []
  end.
Section Sz2.
Variables d0 l0 d1 l1 : ltac2:(SecDiet.SzSec.tyM 'dec_readv_Some2__stmt "vvvv" @d0).
#[using="Type"] Lemma dec_readv_Some2__body : ltac2:(SecDiet.SzSec.bodyP 'dec_readv_Some2__stmt "vvvv").
Proof.
  intros [r ws zs us [|? ?] [|? ?]] a L0 L1 D0 D1 H; try discriminate H.
  unfold dec_readv in H. cbn [core] in H.
  destruct zs; [|discriminate H]. destruct us; [|discriminate H].
  destruct (errno_of r) as [e|] eqn:E.
  - destruct ws; [|discriminate H]. injection H as <-. apply errno_of_Some in E as [-> He]. split; [reflexivity| exact He].
  - unfold iovs_total_Z in H. cbn [fold_right snd fst] in H. rewrite Z.add_0_r in H.
    destruct (Z.leb_spec0 (bv_unsigned r) (l0 + l1)) as [LE|]; [|discriminate H].
    pose proof (bv_unsigned_in_range 64 r) as R. unfold bv_modulus in R. cbn in R.
    set (n := bv_unsigned r) in *.
    cbn [match_scatter] in H.
    destruct (Z.leb_spec0 (Z.min n l0) 0) as [Z0|P0].
    + assert (n = 0) by lia.
      destruct (Z.leb_spec0 (Z.min n l1) 0) as [_|P1]; [|exfalso; lia].
      destruct ws; [|discriminate H].
      replace (n =? 0) with true in H by (symmetry; apply Z.eqb_eq; lia). injection H as <-.
      cbn [length Z.of_nat Z.eqb]. split; [lia|]. f_equal. apply bv_eq. subst n. rewrite H0. reflexivity.
    + destruct ws as [|[x bs0] ws']; [discriminate H|].
      destruct (bv_eqb x (Z_to_bv 64 d0)) eqn:EX; [|discriminate H]. apply bv_eqb_eq' in EX. subst x.
      destruct (Z.eqb_spec (Z.of_nat (length bs0)) (Z.min n l0)) as [EL|]; [|discriminate H]. cbn [andb] in H.
      destruct (Z.leb_spec0 (Z.min (n - Z.min n l0) l1) 0) as [Z1|P1].
      * destruct ws'; [|discriminate H].
        destruct (Z.eqb_spec (n - Z.min n l0) 0) as [E0|]; [|discriminate H]. injection H as <-.
        rewrite app_nil_r. cbn zeta. assert (EN : Z.of_nat (length bs0) = n) by lia.
        split; [lia|]. rewrite EN.
        replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (n <=? l0) with true by (symmetry; apply Z.leb_le; lia).
        f_equal. apply bv_eq. rewrite unsigned_lit by lia. reflexivity.
      * destruct ws' as [|[y bs1] ws'']; [discriminate H|].
        destruct (bv_eqb y (Z_to_bv 64 d1)) eqn:EY; [|discriminate H]. apply bv_eqb_eq' in EY. subst y.
        destruct (Z.eqb_spec (Z.of_nat (length bs1)) (Z.min (n - Z.min n l0) l1)) as [EL1|]; [|discriminate H]. cbn [andb] in H.
        destruct ws''; [|discriminate H].
        destruct (Z.eqb_spec (n - Z.min n l0 - Z.min (n - Z.min n l0) l1) 0) as [E0|]; [|discriminate H]. injection H as <-.
        rewrite app_nil_r. cbn zeta. rewrite length_app.
        assert (EN : Z.of_nat (length bs0 + length bs1) = n) by lia.
        split; [lia|]. rewrite EN.
        replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        replace (n <=? l0) with false by (symmetry; apply Z.leb_gt; lia).
        replace (Z.to_nat l0) with (length bs0) by lia.
        rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r, firstn_all, skipn_app, Nat.sub_diag, skipn_O, skipn_all, app_nil_l.
        f_equal. apply bv_eq. rewrite unsigned_lit by lia. reflexivity.
Qed.
End Sz2.
Lemma dec_readv_Some2 : ltac:(let t := eval cbv delta [dec_readv_Some2__stmt] in dec_readv_Some2__stmt in exact t).
Proof. intros d0 l0 d1 l1. ltac2:(SecDiet.SzSec.closeP 'dec_readv_Some2__body "vvvv"). Qed.

Lemma to_of_bytes : forall l, to_bytes (of_bytes l) = l.
Proof. intros l. unfold to_bytes, of_bytes. rewrite map_map. induction l as [|b l IH]; [reflexivity|]. cbn [map]. rewrite IH. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

(* [comment removed for export] *)
Lemma FR_map : forall l : list byte, Forall (fun z => 0 <= z < 256) (map bv_unsigned l).
Proof. induction l as [|b l IH]; constructor; [pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia| exact IH]. Qed.
Lemma FR_cons : forall (b : byte) l, Forall (fun z => 0 <= z < 256) l -> Forall (fun z => 0 <= z < 256) (bv_unsigned b :: l).
Proof. intros b l H. constructor; [pose proof (bv_unsigned_in_range 8 b) as R; unfold bv_modulus in R; cbn in R; lia| exact H]. Qed.
Lemma FR_app : forall a b : list Z, Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) b -> Forall (fun z => 0 <= z < 256) (a ++ b).
Proof. intros a b Ha Hb. apply Forall_app. split; assumption. Qed.
Lemma FR_firstn : forall k (a : list Z), Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) (firstn k a).
Proof. intros k a H. rewrite <- (firstn_skipn k a) in H. apply Forall_app in H. destruct H as [H _]. exact H. Qed.
Lemma FR_skipn : forall k (a : list Z), Forall (fun z => 0 <= z < 256) a -> Forall (fun z => 0 <= z < 256) (skipn k a).
Proof. intros k a H. rewrite <- (firstn_skipn k a) in H. apply Forall_app in H. destruct H as [_ H]. exact H. Qed.
Ltac frange :=
  repeat first [ assumption | apply Forall_nil | apply FR_map | apply FR_cons | apply FR_app | apply FR_firstn | apply FR_skipn
               | match goal with H : f_rbuf ?f = [] |- Forall _ (f_rbuf ?f) => rewrite H end
               | progress cbn [fst snd f_rbuf set_rbuf set_eof set_w of_bytes] ].
Lemma length_of_bytes : forall l, length (of_bytes l) = length l.
Proof. intros. unfold of_bytes. apply length_map. Qed.

(* [comment removed for export] *)
Lemma apply_mem_write2 : forall m a1 b1 a2 b2,
  apply_writes (apply_zeros (apply_unmaps m []) []) [(a1, b1); (a2, b2)] = write_to_mem (write_to_mem m a1 b1) a2 b2.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Ltac sys_mem_write_inner :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F ?pc ?fc ?rv (write_to_mem (write_to_mem ?m (Z_to_bv 64 ?B) ?bs) ?a2 ?bs2) ?ro) =>
    change (write_to_mem m (Z_to_bv 64 B) bs) with (write_to_mem m (wa B) bs);
    lazymatch goal with
    | H : rw_cells segs m B [CB ?n ?junk] |- _ =>
        let HB := fresh "HB" in
        pose proof (rw_cells_bound segs m B _ H) as HB; cbn [cells_size csize Nat.add] in HB;
        (try lazymatch goal with
         | HI : mem_inv segs m |- _ =>
             let HI' := fresh "MI" in
             pose proof (mem_inv_syswrite segs m B n junk bs HI H ltac:(lia)) as HI'; clear HI; rename HI' into HI
         end);
        let H' := fresh "DST" in
        pose proof (rw_cells_CB_prefix_write segs m B n junk bs H ltac:(lia)) as H';
        clear H;
        transport_chunks segs m B bs;
        footprint_after_store segs m B bs;
        let m' := fresh "m" in
        remember (write_to_mem m (wa B) bs) as m' eqn:Heqm;
        clear Heqm; clear HB; try clear m; rename H' into H
    | _ => fail "sys_mem_write_inner: no hypothesis rw_cells" segs m B "[CB _ _]"
    end
  end.

(* [comment removed for export] *)
Definition iov_bytes0__stmt : Prop := forall m A (w0 w1 w2 w3 : word) rest,
  rw_cells usegs m A (C8 w0 :: C8 w1 :: C8 w2 :: C8 w3 :: rest) ->
  bytes_at usegs m A (iovec_bytes [(w0, w1); (w2, w3)]).
Section Sz11.
Variables m A w0 w1 w2 w3 rest : ltac2:(SecDiet.SzSec.tyM 'iov_bytes0__stmt "vvvvvvv" @m).
#[using="Type"] Lemma iov_bytes0__body : ltac2:(SecDiet.SzSec.bodyP 'iov_bytes0__stmt "vvvvvvv").
Proof.
  intros FR.
  destruct FR as [[WF FB] _]. cbn [cells_bytes cbytes] in FB.
  apply bytes_at_app in FB as [FB0 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB1 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB2 FB]. rewrite length_le8 in FB.
  apply bytes_at_app in FB as [FB3 _].
  cbn [iovec_bytes flat_map fst snd]. rewrite !app_nil_r.
  apply bytes_at_app. rewrite length_app, !length_le8. split.
  - apply bytes_at_app. rewrite length_le8. split; [exact FB0 | exact FB1].
  - apply bytes_at_app. rewrite length_le8. split.
    + replace (A + Z.of_nat (8 + 8)) with (A + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB2.
    + replace (A + Z.of_nat (8 + 8) + Z.of_nat 8) with (A + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 8) by lia. exact FB3.
Qed.
End Sz11.
Lemma iov_bytes0 : ltac:(let t := eval cbv delta [iov_bytes0__stmt] in iov_bytes0__stmt in exact t).
Proof. intros m A w0 w1 w2 w3 rest. ltac2:(SecDiet.SzSec.closeP 'iov_bytes0__body "vvvvvvv"). Qed.

(* [comment removed for export] *)
Definition flags_ok (f : file_st) (flags : word) : Prop :=
  Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0)
  /\ Z.land (bv_unsigned flags) F_NOWR = (if f_nowr f then F_NOWR else 0)
  /\ Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0)
  /\ Z.land (bv_unsigned flags) F_ERR = 0
  /\ Z.land (bv_unsigned flags) F_SVB = 0
  /\ Z.land (bv_unsigned flags) F_PERM = (if f_chan f then F_PERM else 0).   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition land_mod32__stmt : Prop := forall a k, 0 <= k < 2^32 -> 0 <= a -> Z.land (a mod 2^32) k = Z.land a k.
Section Sz12.
Variables a k : ltac2:(SecDiet.SzSec.tyM 'land_mod32__stmt "vv" @a).
#[using="Type"] Lemma land_mod32__body : ltac2:(SecDiet.SzSec.bodyP 'land_mod32__stmt "vv").
Proof.
  intros Hk Ha.
 apply Z.bits_inj'; intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 32) as [L|G].
  - rewrite Z.mod_pow2_bits_low by lia. reflexivity.
  - replace (Z.testbit k i) with false; [rewrite !andb_false_r; reflexivity|].
    symmetry. apply Z.testbit_false; [lia|]. rewrite Z.div_small; [reflexivity|]. split; [lia|].
    eapply Z.lt_le_trans; [apply (proj2 Hk)|]. apply Z.pow_le_mono_r; lia.
Qed.
End Sz12.
Lemma land_mod32 : ltac:(let t := eval cbv delta [land_mod32__stmt] in land_mod32__stmt in exact t).
Proof. intros a k. ltac2:(SecDiet.SzSec.closeP 'land_mod32__body "vv"). Qed.
Lemma sx32_mod32 : forall w : word, bv_unsigned (sx32 w) mod 2^32 = bv_unsigned w mod 2^32.
Proof.
  intros w. unfold sx32. rewrite unsigned_lit_wrap, bv_swrap32_eq.
  pose proof (bv_unsigned_in_range 64 w) as R. unfold bv_modulus in R.
  change (2^64) with 18446744073709551616 in *. change (2^32) with 4294967296. change (2^31) with 2147483648.
  Z.div_mod_to_equations. nia.
Qed.
Lemma lor16_mod32 : forall a, 0 <= a -> Z.lor a 16 mod 2^32 = Z.lor (a mod 2^32) 16.
Proof.
  intros a Ha. rewrite <- !Z.land_ones by lia. rewrite Z.land_lor_distr_l. f_equal.
Qed.
Definition flags_ok_eof__stmt : Prop := forall f (flags : word), flags_ok f flags -> flags_ok (set_eof f) (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)).
Section Sz15.
Variables f flags : ltac2:(SecDiet.SzSec.tyM 'flags_ok_eof__stmt "vv" @f).
#[using="Type"] Lemma flags_ok_eof__body : ltac2:(SecDiet.SzSec.bodyP 'flags_ok_eof__stmt "vv").
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6).
 unfold flags_ok, F_NORD, F_NOWR, F_EOF, F_ERR, F_SVB, F_PERM in *. cbn [f_nord f_nowr f_eof f_chan set_eof].
  pose proof (bv_unsigned_in_range 64 flags) as R. unfold bv_modulus in R.
  rewrite unsigned_lit by (pose proof (Z_lor_range (bv_unsigned flags) 16 ltac:(lia) ltac:(lia)); lia).
  rewrite !Z.land_lor_distr_l. rewrite H1, H2, H4, H5, H6.
  change (Z.land 16 4) with 0. change (Z.land 16 8) with 0. change (Z.land 16 16) with 16. change (Z.land 16 32) with 0. change (Z.land 16 64) with 0. change (Z.land 16 1) with 0.
  rewrite !Z.lor_0_r. repeat split; try reflexivity.
  rewrite H3. destruct (f_eof f); reflexivity.
Qed.
End Sz15.
Lemma flags_ok_eof : ltac:(let t := eval cbv delta [flags_ok_eof__stmt] in flags_ok_eof__stmt in exact t).
Proof. intros f flags. ltac2:(SecDiet.SzSec.closeP 'flags_ok_eof__body "vv"). Qed.

Lemma rw_cells_CB0 : forall m A cs, rw_cells usegs m A cs -> rw_cells usegs m A (CB 0 [] :: cs).
Proof.
  intros m A cs [[W B] R]. split; [split|].
  - cbn. split; [reflexivity | exact W].
  - cbn [cells_bytes cbytes app]. exact B.
  - cbn [cells_size csize]. exact R.
Qed.
Lemma flags_cell_eof : forall m A (flags : word) rest,
  rw_cells usegs m A (C4 (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags)) 16)) :: rest) ->
  rw_cells usegs m A (C4 (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)) :: rest).
Proof.
  intros m A flags rest H. apply (rw_cells_C4_eq m A [] (Z_to_bv 64 (Z.lor (bv_unsigned (sx32 flags)) 16)) (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)) rest); [|exact H].
  pose proof (bv_unsigned_in_range 64 flags) as R1. pose proof (bv_unsigned_in_range 64 (sx32 flags)) as R2. unfold bv_modulus in R1, R2.
  cbn in R1, R2. pose proof (Z_lor_range (bv_unsigned (sx32 flags)) 16 ltac:(lia) ltac:(lia)). pose proof (Z_lor_range (bv_unsigned flags) 16 ltac:(lia) ltac:(lia)).
  rewrite !unsigned_lit by lia.
  rewrite !lor16_mod32 by lia. rewrite sx32_mod32. reflexivity.
Qed.

Section StdioRead.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition rd_inv (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_stdoutw f' = f_stdoutw f /\ f_lbf_nl f' = f_lbf_nl f
    /\ (f_eof f = true -> f_eof f' = true).

  Definition rd_W (sp : word) (Fp B bs D len : Z) : list (Z * Z) :=
    [(bv_unsigned sp - STDIO_READ_DEPTH, bv_unsigned sp); (Fp, Fp + 232); (B, B + bs); (D, D + len)].

  Definition stdio_read_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (closefn readfn seekfn B prev next : Z) (mode : word) (tail : list byte)
      (D len : Z) (djunk : list byte) (lo : Z) (canary : word) (m : mem) : (list Z * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ rd_inv f (snd r) /\ Z.of_nat (length (fst r)) <= len /\
      (Z.of_nat (length (fst r)) < len -> f_rbuf (snd r) = []) /\
      Forall (fun z => 0 <= z < 256) (fst r) /\ Forall (fun z => 0 <= z < 256) (f_rbuf (snd r)) /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (flags' : word) (rp' : Z) (bufbytes' : list byte) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (zlength (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch (rd_W sp Fp B (f_bufsize f) D len) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' Fp (fcells flags' rp' (rp' + zlength (f_rbuf (snd r))) closefn 0 0 0 readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail)
      /\ flags_ok (snd r) flags'
      /\ rw_cells usegs m' B [CB (Z.to_nat (f_bufsize f)) bufbytes']
      /\ (f_rbuf (snd r) <> [] -> B <= rp' /\ rp' + zlength (f_rbuf (snd r)) <= B + f_bufsize f
                                /\ firstn (length (f_rbuf (snd r))) (skipn (Z.to_nat (rp' - B)) bufbytes') = to_bytes (f_rbuf (snd r)))
      /\ 0 <= rp' /\ rp' + zlength (f_rbuf (snd r)) < 2^63
      /\ rw_cells usegs m' D [CB (length (fst r)) (to_bytes (fst r)); CB (Z.to_nat len - length (fst r)) (skipn (length (fst r)) djunk)]
      /\ ssp_cells m' canary.

  Definition stdio_read_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rp closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (D len : Z) (djunk : list byte) (lo : Z) (canary : word),
      rw_cells usegs m Fp (fcells flags rp rp closefn 0 0 0 readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      flags_ok f flags -> 0 <= rp < 2^63 ->
      rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] ->
      rw_cells usegs m D [CB (Z.to_nat len) djunk] ->
      f_wactive f = false -> f_wbuf f = [] -> f_rbuf f = [] -> f_chan f = false -> 3 <= f_fd f < 2^31 ->
      a0 = Z_to_bv 64 Fp -> a1 = Z_to_bv 64 D -> a2 = Z_to_bv 64 len ->
      1 <= len -> 0 < f_bufsize f <= 2^20 -> len <= 2^30 ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - STDIO_READ_DEPTH -> 0x56000 <= lo -> bv_unsigned sp <= 2^47 ->
      ssp_cells m canary -> mem_inv usegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      (B + f_bufsize f <= got_ssp \/ got_ssp + 8 <= B) -> (B + f_bufsize f <= ssp_guard \/ ssp_guard + 8 <= B) ->
      (D + len <= got_ssp \/ got_ssp + 8 <= D) -> (D + len <= ssp_guard \/ ssp_guard + 8 <= D) ->
      0 < B -> B + f_bufsize f <= 2^47 -> 0 <= D -> D + len <= 2^47 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) -> (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      (D + len <= lo \/ bv_unsigned sp <= D) -> (D + len <= Fp \/ Fp + 232 <= D) -> (D + len <= B \/ B + f_bufsize f <= D) ->
      implM usegs (stdio_read f B D len) st
        (stdio_read_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp closefn readfn seekfn B prev next mode tail D len djunk lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 STDIO_READ) fc None m (seg_rom usegs)).
  Section Sz18.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn seekfn B prev next mode tail bufbytes D len djunk lo canary : ltac2:(SecDiet.SzSec.tyM 'stdio_read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma stdio_read_spec__body : ltac2:(SecDiet.SzSec.bodyP 'stdio_read_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros FC FL RPR BUF DST WACT WB0 RB0 NCH FD -> -> -> L1 BS LMAX ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 BSEP1 BSEP2 DSEP1 DSEP2 B0 B47 D0 D47 SB1 SB2 SD1 SD2 SD3.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold STDIO_READ, STDIO_READ_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (rd_W sp Fp B (f_bufsize f) D len) m) as MU. pose proof (wmono_refl usegs m) as WM. unfold rd_W, STDIO_READ_DEPTH in MU.
    unfold fcells, file_cells in FC.
    unfold stdio_read.
    replace (f_bufsize f =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn zeta.
    apply implM_prefix.
    carve_frame 80%nat ST.
    do 13 zs. do 3 zs. rewrite (sx32_small (f_fd f)) by lia.
    do 6 zs.
    assert (HB1 : (0 <? f_bufsize f) = true) by (apply Z.ltb_lt; lia). rewrite HB1 in *. cbn [Z.b2z] in *.
    destruct (Z.eq_dec len 1) as [L1eq | Lgt].
    - (* [comment removed for export] *)
      subst len. change (1 - 1 =? 0) with true. cbv iota. change (1 - 1) with 0 in *.
      zs. if_true. zs.
      apply evt_done. apply implM_sys_bind.
      step_ecall. split.
      { at_node_red; split_spine; try reflexivity; try lia.
        - unfold max_read. lia.   (* [comment removed for export] *)
        - apply (rw_cells_wr_at usegs _ _ _ _ BUF). cbn [cells_size csize]. lia. }
      intros rsp ans Hdec.
      apply (dec_read_Some B (f_bufsize f)) in Hdec; [| lia].
      destruct ans as [e | raw].
      { apply implM_unr. }
      destruct Hdec as [-> NLE].
      unfold zlength. rewrite length_of_bytes.
      destruct raw as [|b0 rest2].
      + (* [comment removed for export] *)
        cbn [length Z.of_nat Z.eqb delivered_writes].
        apply implM_prefix. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x1b150)) with (Z_to_bv 64 0x1b150 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. lia. }
        zs. if_true. zs. zs. zs. zs. zs.
        do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. apply implM_ret. apply evt_done.
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        apply flags_cell_eof in FC.
        unfold stdio_read_post. cbn [fst snd f_rbuf set_eof length of_bytes map].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)), rp, bufbytes, mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
        split; [unfold fcells, file_cells; exact FC|]. split; [apply flags_ok_eof; exact FL|].
        split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
        split; [apply rw_cells_CB0; exact DST|]. split; [exact GOT | exact GUARD].
      + (* [comment removed for export] *)
        cbn [delivered_writes].
        set (raw' := b0 :: rest2) in *. assert (ER : raw' = b0 :: rest2) by reflexivity. assert (LRW : length raw' = S (length rest2)) by reflexivity.
        clearbody raw'. cbn [length] in NLE.
        replace (Z.of_nat (length raw') =? 0) with false by (rewrite LRW; reflexivity).
        replace (Z.of_nat (length raw') <=? 0) with false by (rewrite LRW; reflexivity).
        apply implM_prefix. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x1b150)) with (Z_to_bv 64 0x1b150 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        zs. if_cases Hp; zify_cond Hp. 2:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
        zs. zs. if_cases Hq; zify_cond Hq. 1:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
        zs. zs. zs. zs. zs. zs.
        zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
        zs. zs.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
        assert (HR : ov_read_bytes usegs mC (wa (B + 0)) 1 = Some [b0]).
        { pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BB. cbn [cells_bytes cbytes] in BB. rewrite ER in BB.
          rewrite (bytes_at_read usegs mC B _ 0 1 BB); [reflexivity | lia | cbn; rewrite length_app; cbn; lia]. }
        zs. zs.
        assert (HS : store_ok usegs mC (wa (D + 0)) 1 = true).
        { apply (wr_at_store_ok usegs mC D 1 0 1); [| lia | lia].
          apply (rw_cells_wr_at usegs _ _ _ _ DST). cbn [cells_size csize]. lia. }
        zs.
        change (Z_to_bv 64 (bv_unsigned b0)) with (zxb b0). rewrite le1_zxb.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ ?a _) _) =>
          replace a with (wa D) by (unfold wa; f_equal; lia) end.
        pose proof (rw_cells_CB_prefix_write usegs mC D _ _ [b0] DST ltac:(cbn; lia)) as DST2. cbn [length] in DST2.
        store_done.
        zs. do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. apply implM_ret. apply evt_done.
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        subst raw'. cbn [length] in LRW, NLE.
        pose proof (rw_cells_merge usegs mZ B [] [CB (length (b0 :: rest2)) (b0 :: rest2); CB (Z.to_nat (f_bufsize f) - length (b0 :: rest2)) (skipn (length (b0 :: rest2)) bufbytes)] []) as BM.
        cbn [app] in BM. specialize (BM BUF). cbn [cells_size cells_bytes csize cbytes app Nat.add] in BM. rewrite app_nil_r in BM.
        replace (length (b0 :: rest2) + (Z.to_nat (f_bufsize f) - length (b0 :: rest2) + 0))%nat with (Z.to_nat (f_bufsize f)) in BM by (cbn [length] in NLE |- *; lia).
        unfold stdio_read_post. cbn [fst snd]. replace (Z.to_nat 0) with 0%nat by reflexivity. cbn [of_bytes map f_rbuf set_rbuf]. rewrite !skipn_O, !firstn_O.
        repeat match goal with |- context [skipn 1 (?a :: ?l)] => change (skipn 1 (a :: l)) with l end.
        repeat match goal with |- context [firstn 1 (?a :: ?l)] => change (firstn 1 (a :: l)) with [a] end.
        cbn [app length].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros HH; exfalso; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists flags, (B + 1), ((b0 :: rest2) ++ skipn (length (b0 :: rest2)) bufbytes), mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        unfold zlength. rewrite ?length_map.
        split. { unfold fcells, file_cells. replace (B + 1 + Z.of_nat (length rest2)) with (B + (Z.of_nat (length (b0 :: rest2)) - 0)) by (cbn [length]; lia). exact FC. }
        split; [exact FL|].
        split; [exact BM|].
        split. { intros _. rewrite ?length_map. split; [lia|]. split; [lia|]. replace (Z.to_nat (B + 1 - B)) with 1%nat by lia. rewrite <- app_comm_cons.
                 repeat match goal with |- context [skipn 1 (?a :: ?l)] => change (skipn 1 (a :: l)) with l end.
                 rewrite firstn_app, Nat.sub_diag, firstn_O, app_nil_r. fold (of_bytes rest2). rewrite to_of_bytes. apply firstn_all2. lia. }
        split; [lia|]. split; [lia|].
        split. { cbn [length Nat.sub]. change (to_bytes [bv_unsigned b0]) with (to_bytes (of_bytes [b0])). rewrite to_of_bytes. exact DST2. }
        split; [exact GOT | exact GUARD].
    - (* [comment removed for export] *)
      replace (len - 1 =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
      zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs.
      apply evt_done. apply implM_sys_bind.
      step_ecall. split.
      { lazymatch goal with |- at_node _ _ (MSsvc _ _ _ _ _ _ ?mm _) =>
          lazymatch goal with FRM : rw_cells usegs mm (bv_unsigned sp + -80) _ |- _ =>
            pose proof (iov_bytes0 _ _ _ _ _ _ _ FRM) as IOV end end.
        at_node_red; split_spine.
        - reflexivity.
        - lia.
        - reflexivity.
        - reflexivity.
        - cbn; lia.
        - rewrite unsigned_lit by lia. cbn [length Z.of_nat]. lia.
        - lia.
        - cbn [dsts_total]. unfold MAX_RW_COUNT. lia.
        - constructor; [|constructor; [|constructor]]; cbn [fst snd].
          + split; [lia|]. split; [lia|].
            apply (rw_cells_wr_at usegs _ _ _ _ DST). cbn [cells_size csize]. lia.
          + split; [lia|]. split; [lia|].
            apply (rw_cells_wr_at usegs _ _ _ _ BUF). cbn [cells_size csize]. lia.
        - reflexivity.
        - rewrite unsigned_lit by lia. cbn [iovs_of map fst snd]. exact IOV. }
      intros rsp ans Hdec.
      apply (dec_readv_Some2 D (len - 1) B (f_bufsize f)) in Hdec; [| lia | lia | lia | lia].
      destruct ans as [e | raw].
      { (* [comment removed for export] *) apply implM_unr. }
      cbv zeta in Hdec. destruct Hdec as [NLE ->].
      set (n := Z.of_nat (length raw)) in *.
      unfold zlength. rewrite length_of_bytes. fold n.
      destruct (Z.eqb_spec n 0) as [N0 | N0].
      + (* [comment removed for export] *)
        replace (n =? 0) with true by (symmetry; apply Z.eqb_eq; exact N0).
        apply implM_prefix. sys_nret.
        step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
        step.
        replace (ret_pc (Z_to_bv 64 0x1b104)) with (Z_to_bv 64 0x1b104 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        rewrite N0. zs. if_true. zs. if_true. zs. zs. zs. zs. zs.
        (* [comment removed for export] *)
        do 3 zs. if_false. do 8 zs.
        release_frame FR ST (bv_unsigned sp).
        apply evt_done. apply implM_ret. apply evt_done.
        assert (raw = []) as -> by (destruct raw; [reflexivity | exfalso; subst n; cbn in N0; lia]).
        lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
        apply flags_cell_eof in FC.
        unfold stdio_read_post. cbn [fst snd f_rbuf set_eof length of_bytes map].
        split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|]. split; [lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
        do 14 eexists. exists (Z_to_bv 64 (Z.lor (bv_unsigned flags) 16)), rp, bufbytes, mZ.
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
        rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r, Nat.sub_0_r.
        split; [unfold fcells, file_cells; exact FC|]. split; [apply flags_ok_eof; exact FL|].
        split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
        split; [apply rw_cells_CB0; exact DST|]. split; [exact GOT | exact GUARD].
      + replace (n =? 0) with false by (symmetry; apply Z.eqb_neq; exact N0).
        destruct (Z.leb_spec0 n (len - 1)) as [LE1 | GT1].
        * (* [comment removed for export] *)
          replace (n <=? len - 1) with true by (symmetry; apply Z.leb_le; exact LE1).
          apply implM_prefix. sys_nret.
          step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
          step.
          replace (ret_pc (Z_to_bv 64 0x1b104)) with (Z_to_bv 64 0x1b104 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
          zs. zs. if_cases Hq; zify_cond Hq. 2:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
          zs. zs.
          do 3 zs. if_false. do 8 zs.
          release_frame FR ST (bv_unsigned sp).
          apply evt_done. apply implM_ret. apply evt_done.
          lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
          unfold stdio_read_post. cbn [fst snd].
          split; [reflexivity|]. split; [unfold rd_inv; repeat split; auto|]. split; [rewrite length_of_bytes; lia|]. split; [intros _; exact RB0|]. split; [solve [frange]|]. split; [solve [frange]|].
          do 14 eexists. exists flags, rp, bufbytes, mZ.
          split; [cbv delta [mkR]; unfold zlength; rewrite length_of_bytes; reflexivity|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          rewrite RB0. unfold zlength. cbn [length Z.of_nat]. rewrite Z.add_0_r.
          split; [unfold fcells, file_cells; exact FC|]. split; [exact FL|].
          split; [exact BUF|]. split; [intros HH; exfalso; exact (HH eq_refl)|]. split; [lia|]. split; [lia|].
          split; [rewrite to_of_bytes, length_of_bytes; exact DST|]. split; [exact GOT | exact GUARD].
        * (* [comment removed for export] *)
          replace (n <=? len - 1) with false by (symmetry; apply Z.leb_gt; lia).
          apply implM_prefix.
          rewrite nret_MSsvc; rewrite ?mkR_set_a0; simp_regs.
          lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?p + Z_to_bv 64 4)%bv _ _ _ _) =>
              let p' := eval vm_compute in (p + 4)%Z in
              replace (Z_to_bv 64 p + Z_to_bv 64 4)%bv with (Z_to_bv 64 p' : word) by (rewrite lit_add_lit; reflexivity)
          end.
          rewrite apply_mem_write2.
          assert (LF : length (firstn (Z.to_nat (len - 1)) raw) = Z.to_nat (len - 1)) by (rewrite length_firstn; lia).
          assert (LS : length (skipn (Z.to_nat (len - 1)) raw) = (length raw - Z.to_nat (len - 1))%nat) by (rewrite length_skipn; lia).
          sys_mem_write_inner.
          sys_mem_write.
          rewrite LF in DST. rewrite LS in BUF.
          assert (exists b0 rest2, skipn (Z.to_nat (len - 1)) raw = b0 :: rest2) as (b0 & rest2 & EB2).
          { destruct (skipn (Z.to_nat (len - 1)) raw) as [|b0 r2] eqn:E; [exfalso; cbn in LS; lia | exists b0, r2; reflexivity]. }
          rewrite EB2 in BUF. cbn [length] in BUF.
          step. step. step. step. if_cases Hr; zify_cond Hr. 2:{ exfalso. lia. }
          step.
          replace (ret_pc (Z_to_bv 64 0x1b104)) with (Z_to_bv 64 0x1b104 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
          zs. if_cases Hp; zify_cond Hp. 1:{ exfalso. rewrite ?Z.mod_small in Hp by lia. lia. }
          zs. zs. if_cases Hq; zify_cond Hq. 1:{ exfalso. rewrite ?Z.mod_small in Hq by lia. lia. }
          zs. zs. zs. zs. zs. zs.
          zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. rewrite ?Z.mod_small in Hb by lia. lia. }
          zs. zs.
          lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mC end.
          assert (HR : ov_read_bytes usegs mC (wa (B + 0)) 1 = Some [b0]).
          { pose proof (rw_cells_bytes_at _ _ _ _ BUF) as BB. cbn [cells_bytes cbytes] in BB.
            rewrite (bytes_at_read usegs mC B _ 0 1 BB); [reflexivity | lia | cbn; rewrite length_app; cbn; lia]. }
          zs. zs.
          assert (HS : store_ok usegs mC (wa (D + (len - 1))) 1 = true).
          { apply (wr_at_store_ok usegs mC D len (len - 1) 1); [| lia | lia].
            apply (rw_cells_wr_at usegs _ _ _ _ DST). cbn [cells_size csize]. lia. }
          zs.
          change (Z_to_bv 64 (bv_unsigned b0)) with (zxb b0). rewrite le1_zxb.
          (* [comment removed for export] *)
          set (k := Z.to_nat (len - 1)) in *.
          pose proof DST as DST0.
          apply (proj1 (rw_cells_app usegs _ _ [_] [_])) in DST0. destruct DST0 as [DSTa DSTb].
          cbn [cells_size csize Nat.add] in DSTb. rewrite Nat.add_0_r in DSTb.
          assert (DST2 : rw_cells usegs (write_to_mem mC (wa (D + (len - 1))) [b0]) D
                           [CB (k + 1) (firstn k raw ++ [b0]); CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))]).
          { replace (D + (len - 1)) with (D + Z.of_nat k) by lia.
            assert (A1 : rw_cells usegs (write_to_mem mC (wa (D + Z.of_nat k)) [b0]) D [CB k (firstn k raw)]).
            { apply rw_cells_frame; [exact DSTa | lia | cbn; lia | cbn [cells_size csize length]; lia]. }
            pose proof (rw_cells_CB_prefix_write usegs mC (D + Z.of_nat k) _ _ [b0] DSTb ltac:(cbn; lia)) as A2. cbn [length] in A2.
            pose proof (proj2 (rw_cells_app usegs (write_to_mem mC (wa (D + Z.of_nat k)) [b0]) D [CB k (firstn k raw)] [CB 1 [b0]; CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))])) as J.
            cbn [cells_size csize Nat.add app] in J. rewrite ?Nat.add_0_r in J. specialize (J (conj A1 A2)).
            apply (rw_cells_merge usegs _ D [] [CB k (firstn k raw); CB 1 [b0]] [CB (Z.to_nat len - k - 1) (skipn 1 (skipn k djunk))]) in J.
            cbn [cells_size cells_bytes csize cbytes app Nat.add] in J. rewrite ?Nat.add_0_r, ?app_nil_r in J. exact J. }
          clear DSTa DSTb.
          store_done.
          zs. do 3 zs. if_false. do 8 zs.
          release_frame FR ST (bv_unsigned sp).
          apply evt_done. apply implM_ret. apply evt_done.
          lazymatch goal with |- _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mZ end.
          (* [comment removed for export] *)
          pose proof (rw_cells_merge usegs mZ B [] [CB (length raw - k) (b0 :: rest2); CB (Z.to_nat (f_bufsize f) - (length raw - k)) (skipn (length raw - k) bufbytes)] []) as BM.
          cbn [app] in BM. specialize (BM BUF). cbn [cells_size cells_bytes csize cbytes app Nat.add] in BM. rewrite app_nil_r in BM.
          replace (length raw - k + (Z.to_nat (f_bufsize f) - (length raw - k) + 0))%nat with (Z.to_nat (f_bufsize f)) in BM by lia.
          assert (RB : skipn 1 (skipn k (of_bytes raw)) = of_bytes rest2).
          { unfold of_bytes. rewrite !skipn_map, EB2. reflexivity. }
          assert (HD : firstn k (of_bytes raw) ++ firstn 1 (skipn k (of_bytes raw)) = of_bytes (firstn k raw ++ [b0])).
          { unfold of_bytes. rewrite firstn_map, skipn_map, EB2, map_app. reflexivity. }
          assert (LR2 : Z.of_nat (length rest2) = n - len).
          { apply (f_equal (@length byte)) in EB2. rewrite length_skipn in EB2. cbn [length] in EB2. lia. }
          unfold stdio_read_post. cbn [fst snd]. rewrite RB, HD. cbn [f_rbuf set_rbuf].
          split; [reflexivity|]. split; [unfold rd_inv; cbn; repeat split; auto|].
          split; [rewrite length_of_bytes, length_app; cbn [length]; lia|].
          split; [rewrite length_of_bytes, length_app; cbn [length]; intros HH; exfalso; lia|]. split; [solve [frange]|]. split; [solve [frange]|].
          do 14 eexists. exists flags, (B + 1), ((b0 :: rest2) ++ skipn (length raw - k) bufbytes), mZ.
          split; [cbv delta [mkR]; unfold zlength; rewrite length_of_bytes, length_app; cbn [length]; repeat f_equal; lia|].
          split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
          unfold zlength. rewrite !length_of_bytes.
          split. { unfold fcells, file_cells. replace (B + 1 + Z.of_nat (length rest2)) with (B + (n - (len - 1))) by lia. exact FC. }
          split; [exact FL|].
          split; [exact BM|].
          split. { intros _. split; [lia|]. split; [lia|]. replace (Z.to_nat (B + 1 - B)) with 1%nat by lia. rewrite <- app_comm_cons. cbn [skipn].
                   rewrite ?skipn_O, ?length_of_bytes, firstn_app, Nat.sub_diag, firstn_O, app_nil_r, to_of_bytes. apply firstn_all2. lia. }
          split; [lia|]. split; [lia|].
          split. { rewrite to_of_bytes, length_app, length_firstn. cbn [length].
                   replace (Nat.min k (length raw) + 1)%nat with (k + 1)%nat by lia.
                   rewrite skipn_skipn in DST2. replace (1 + k)%nat with (k + 1)%nat in DST2 by lia.
                   replace (Z.to_nat len - (k + 1))%nat with (Z.to_nat len - k - 1)%nat by lia. exact DST2. }
          split; [exact GOT | exact GUARD].
  Qed.
  End Sz18.
  Theorem stdio_read_spec : ltac:(let t := eval cbv delta [stdio_read_spec__stmt] in stdio_read_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn seekfn B prev next mode tail bufbytes D len djunk lo canary. ltac2:(SecDiet.SzSec.closeP 'stdio_read_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End StdioRead.
End TwB.
End F_stdio_read.

(* [comment removed for export] *)
Module F_toread.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TOREAD : Z := 0x1ade8.
Definition TOREAD_TAIL : Z := 0x1ae28.
Definition TOREAD_DEPTH : Z := 160.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bit4_decomp : forall X, 0 <= X -> X = 32 * (X / 32) + 16 * ((X / 16) mod 2) + X mod 16.
Proof.
  intros X HX.
  rewrite (Z.div_mod X 16) at 1 by lia.
  replace (X / 16) with (2 * (X / 16 / 2) + (X / 16) mod 2) at 1 by (symmetry; rewrite <- Z.div_mod by lia; reflexivity).
  rewrite Z.div_div by lia. change (16 * 2) with 32. lia.
Qed.

Definition sra_bit4__stmt : Prop := forall X, 0 <= X < 2^32 ->
  Z.shiftr (((Z.shiftl X 59 mod 2^64) + 2^63) mod 2^64 - 2^63) 63 = - ((X / 16) mod 2).
Section Sz2.
Variables X : ltac2:(SecDiet.SzSec.tyM 'sra_bit4__stmt "v" @X).
#[using="Type"] Lemma sra_bit4__body : ltac2:(SecDiet.SzSec.bodyP 'sra_bit4__stmt "v").
Proof.
  intros HX.
 rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (bit4_decomp X ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound X 16 ltac:(lia)) as R.
  pose proof (Z.mod_pos_bound (X / 16) 2 ltac:(lia)) as B.
  set (q := X / 32) in *. set (b := (X / 16) mod 2) in *. set (r := X mod 16) in *.
  rewrite D.
  replace ((32 * q + 16 * b + r) * 2 ^ 59) with (b * 2^63 + r * 2^59 + q * 2^64) by lia.
  rewrite Z.mod_add by lia.
  assert (b = 0 \/ b = 1) as [-> | ->] by lia.
  - rewrite (Z.mod_small (0 * 2^63 + r * 2^59)) by lia. rewrite Z.mod_small by lia.
    apply Z.div_small. lia.
  - replace (1 * 2 ^ 63 + r * 2 ^ 59) with (r * 2^59 + 2^63) by lia.
    rewrite (Z.mod_small (r * 2^59 + 2^63)) by lia.
    replace (r * 2 ^ 59 + 2 ^ 63 + 2 ^ 63) with (r * 2^59 + 1 * 2^64) by lia. rewrite Z.mod_add, Z.mod_small by lia.
    symmetry. apply Z.div_unique_pos with (r := r * 2^59); lia.
Qed.
End Sz2.
Lemma sra_bit4 : ltac:(let t := eval cbv delta [sra_bit4__stmt] in sra_bit4__stmt in exact t).
Proof. intros X. ltac2:(SecDiet.SzSec.closeP 'sra_bit4__body "v"). Qed.

Lemma testbit_16 : forall i, 0 <= i -> Z.testbit 16 i = (i =? 4).
Proof. intros i Hi. change 16 with (2^4). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_sym. Qed.
Definition land16_bit4__stmt : Prop := forall X, 0 <= X -> Z.land X 16 = 16 * ((X / 16) mod 2).
Section Sz4.
Variables X : ltac2:(SecDiet.SzSec.tyM 'land16_bit4__stmt "v" @X).
#[using="Type"] Lemma land16_bit4__body : ltac2:(SecDiet.SzSec.bodyP 'land16_bit4__stmt "v").
Proof.
  intros HX.
 pose proof (Z.mod_pos_bound (X / 16) 2 ltac:(lia)) as B.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_16 by lia.
  assert ((X / 16) mod 2 = 0 \/ (X / 16) mod 2 = 1) as [E|E] by lia; rewrite E.
  - rewrite Z.mul_0_r, Z.bits_0. destruct (Z.eqb_spec i 4); [subst|apply andb_false_r].
    rewrite andb_true_r. apply Z.testbit_false; [lia|]. change (2^4) with 16. exact E.
  - rewrite Z.mul_1_r, testbit_16 by lia. destruct (Z.eqb_spec i 4); [subst|apply andb_false_r].
    rewrite andb_true_r. apply Z.testbit_true; [lia|]. change (2^4) with 16. exact E.
Qed.
End Sz4.
Lemma land16_bit4 : ltac:(let t := eval cbv delta [land16_bit4__stmt] in land16_bit4__stmt in exact t).
Proof. intros X. ltac2:(SecDiet.SzSec.closeP 'land16_bit4__body "v"). Qed.
(* [comment removed for export] *)
Lemma land_low32 : forall X k, 0 <= k < 2^32 -> Z.land (X mod 2^32) k = Z.land X k mod 2^32.
Proof.
  intros X k Hk. rewrite <- !Z.land_ones by lia.
  rewrite (Z.land_comm (Z.land X k)), Z.land_assoc, (Z.land_comm (Z.ones 32) X). reflexivity.
Qed.

Lemma CB_prefix_bytes_at' : forall m A n (bb : list byte) (p : list byte),
  rw_cells ssegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at ssegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.
Lemma wfn_after_write' : forall f, wfn_of (f_after_write f) = F_STDIO_WRITE.
Proof. intros f. unfold wfn_of, f_after_write. destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; reflexivity. Qed.

Section Toread.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition tr_inv (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = []
    /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

  Definition tr_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - TOREAD_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  Definition toread_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte)
      (lo : Z) (canary : word) (m : mem) : (bool * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ fst r = f_eof f /\ tr_inv f (snd r) /\ f_nord f = false /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (- Z.b2z (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch (tr_W sp Fp) m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' Fp (fcells flags (B + f_bufsize f) (B + f_bufsize f) closefn 0 0 0 readfn (wfn_of (snd r)) seekfn B (f_bufsize f) prev next (f_fd f) mode' (lbf_of (snd r)) tail)
      /\ ssp_cells m' canary.

  Section Tail.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis FLN : Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0).
    Hypothesis FLE : Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0).
    Hypothesis LO : lo <= bv_unsigned sp - TOREAD_DEPTH.
    Hypothesis GLO : 0x55000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis B0 : 0 < B.
    Hypothesis BShi : B + f_bufsize f <= 2^47.   (* [comment removed for export] *)
    Hypothesis BS0 : 0 <= f_bufsize f.

    (* [comment removed for export] *)
    Definition toread_tail__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells ssegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      rw_cells ssegs m1 Fp (fcells flags 0 0 closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) \/
      (exists rp re, rw_cells ssegs m1 Fp (fcells flags rp re closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail)) ->
      ssp_cells m1 canary -> stk ssegs m1 lo (bv_unsigned sp + -16) -> mem_inv ssegs m1 ->
      munch (tr_W sp Fp) m m1 -> wmono ssegs m m1 ->
      tr_inv f (set_rbuf [] (set_w false [] f1)) ->
      implM ssegs (let f2 := set_w false [] f1 in if f_nord f2 then munr else mret (f_eof f2, set_rbuf [] f2)) st
        (toread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TOREAD_TAIL) fc None m1 (seg_rom ssegs)).
    Section Sz8.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'toread_tail__stmt "vvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma toread_tail__body : ltac2:(SecDiet.SzSec.bodyP 'toread_tail__stmt "vvvvvvvvvvvvvvvvvvvvvv").
    Proof using FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO. pin_using (fun (FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
      intros FR1 FC1 SSP1 ST1 MI1 MU1 WM1 INV.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (bv_unsigned_in_range 64 flags) as FLR. unfold bv_modulus in FLR. cbn in FLR.
      assert (FC : exists rp re, rw_cells ssegs m1 Fp (fcells flags rp re closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail)).
      { destruct FC1 as [H | H]; [exists 0, 0; exact H | exact H]. }
      clear FC1. destruct FC as (rp & re & FC).
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold tr_W, TOREAD_DEPTH, TOREAD_TAIL in *. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
      cbv zeta. cbn [f_nord f_eof set_w].
      pose proof INV as INV'. destruct INV as (If1 & If2 & If3 & If4 & If5 & If6 & _). cbn [set_rbuf set_w f_nord f_eof f_fd f_bufsize f_chan f_nowr] in If1, If2, If3, If4, If5, If6.
      rewrite If4, If6.
      apply implM_prefix.
      zs. zs.
      replace (Z.land (bv_unsigned (zx32 flags)) 4) with (if f_nord f then 4 else 0).
      2:{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
          rewrite land_low32 by lia. unfold F_NORD in FLN. rewrite FLN. destruct (f_nord f); reflexivity. }
      zs. zs. zs.
      destruct (f_nord f) eqn:NORD.
      { (* [comment removed for export] *) apply evt_done. apply implM_unr. }
      zs. if_false. zs. zs. zs. zs. zs. zs. zs.
      assert (X32 : bv_unsigned (zx32 flags) = bv_unsigned flags mod 2^32).
      { unfold zx32. apply unsigned_lit. pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)). lia. }
      assert (EB : (bv_unsigned (zx32 flags) / 16) mod 2 = Z.b2z (f_eof f)).
      { rewrite X32. pose proof (land16_bit4 (bv_unsigned flags mod 2^32) ltac:(apply Z.mod_pos_bound; lia)) as L.
        rewrite land_low32 in L by lia. unfold F_EOF in FLE. rewrite FLE in L.
        pose proof (Z.mod_pos_bound (bv_unsigned flags mod 2 ^ 32 / 16) 2 ltac:(lia)).
        destruct (f_eof f); cbn [Z.b2z]; [change (16 mod 2^32) with 16 in L | change (0 mod 2^32) with 0 in L]; lia. }
      replace (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zx32 flags)) 59))) 63) with (- Z.b2z (f_eof f)).
      2:{ rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
          change (2 ^ Z.of_N 64) with (2^64). change (2^64 `div` 2) with (2^63).
          rewrite <- (Zplus_mod_idemp_l (Z.shiftl (bv_unsigned (zx32 flags)) 59)).
          rewrite sra_bit4 by (rewrite X32; pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
          rewrite EB. reflexivity. }
      zs. zs. zs. zs. zs.
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evt_done. apply implM_ret. apply evt_done.
      unfold toread_post. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [exact INV'|]. split; [exact NORD|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz8.
    Lemma toread_tail : ltac:(let t := eval cbv delta [toread_tail__stmt] in toread_tail__stmt in exact t).
    Proof using FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'toread_tail__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End Tail.

  Lemma implM_retb : forall {A B} (a : A) (k : A -> M St B) (s : St) Q ms,
    implM ssegs (k a) s Q ms -> implM ssegs (mbind (mret a) k) s Q ms.
  Proof using Type. pin_using tt. intros A B a k s Q ms H. exact H. Qed.

  Definition toread_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (lo : Z) (canary : word),
      rw_cells ssegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0) ->
      Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> f_rbuf f = [] ->
      a0 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - TOREAD_DEPTH -> 0x55000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv ssegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      implM ssegs (toread f) st
        (toread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TOREAD) fc None m (seg_rom ssegs)).
  Section Sz10.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'toread_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma toread_spec__body : ltac2:(SecDiet.SzSec.bodyP 'toread_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FLN FLE FL64 BUF BUFP WB0 RB0 -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BShi BS0 WBL BSZ SEPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold TOREAD, TOREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (tr_W sp Fp) m) as MU. pose proof (wmono_refl ssegs m) as WM. unfold tr_W, TOREAD_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'.
    assert (TRI : forall f1, f_fd f1 = f_fd f -> f_chan f1 = f_chan f -> f_bufsize f1 = f_bufsize f -> f_nord f1 = f_nord f -> f_nowr f1 = f_nowr f -> f_eof f1 = f_eof f ->
                  (f_stdoutw f1 = true -> f_stdoutw f = true) -> (f_lbf_nl f1 = true -> f_lbf_nl f = true) -> tr_inv f (set_rbuf [] (set_w false [] f1))).
    { intros f1 E1 E2 E3 E4 E5 E6 E7 E8. unfold tr_inv. cbn. repeat split; auto. }
    unfold toread.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      apply implM_prefix.
      carve_frame 16%nat ST.
      do 10 zs. zs.
      if_true.
      apply evt_done.
      eapply toread_tail with (f1 := f); fastfirst (first
        [ noevar_assumption | exact FLN | exact FLE | exact FR | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD] | exact MI | exact MU | exact WM
        | right; eexists _, _; unfold fcells, file_cells; exact FC
        | apply TRI; auto
        | split; assumption | assumption | lia
        ]).
    - (* [comment removed for export] *)
      replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
        by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
      assert (WACT : f_wactive f = true).
      { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
      rewrite WACT in FC.
      assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
      unfold fcells, file_cells in FC.
      change (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
      apply implM_prefix.
      carve_frame 16%nat ST.
      do 10 zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evt_done.
      unfold boxed in BUF.
      assert (BUFB : bytes_at ssegs m0 B (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP].
        eapply (rw_cells_transport ssegs _ m m0); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      eapply implM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
          (seekfn := seekfn) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: fastfirst (first [ noevar_assumption | reflexivity | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                   | apply bytes_at_nil; lia
                   | generalize CH; destruct (f_chan f); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; cbn; lia]]
                   | left; reflexivity
                   | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia
                   | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                   ]). }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x1ae28)) with (Z_to_bv 64 0x1ae28 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR2 : rw_cells ssegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
      { eapply (rw_cells_transport ssegs _ m0 m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      eapply toread_tail with (f1 := f_after_write f); fastfirst (first
        [ noevar_assumption | exact FLN | exact FLE | exact FR2 | exact SSP2 | exact MI2 | exact ST2
        | apply (munch_trans _ m m0 m2); [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp, tr_W, TOREAD_DEPTH; cbn [outside]; intros; lia]
        | eapply wmono_trans; [exact WM | exact WM2]
        | right; eexists _, _; rewrite wfn_after_write'; exact FC2
        | apply TRI; unfold f_after_write; destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; auto; intros HH; discriminate HH
        | assumption | lia
        ]).
  Qed.
  End Sz10.
  Theorem toread_spec : ltac:(let t := eval cbv delta [toread_spec__stmt] in toread_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'toread_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Toread.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition TOREAD : Z := 0x1b5a8.
Definition TOREAD_TAIL : Z := 0x1b5e8.
Definition TOREAD_DEPTH : Z := 160.   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bit4_decomp : forall X, 0 <= X -> X = 32 * (X / 32) + 16 * ((X / 16) mod 2) + X mod 16.
Proof.
  intros X HX.
  rewrite (Z.div_mod X 16) at 1 by lia.
  replace (X / 16) with (2 * (X / 16 / 2) + (X / 16) mod 2) at 1 by (symmetry; rewrite <- Z.div_mod by lia; reflexivity).
  rewrite Z.div_div by lia. change (16 * 2) with 32. lia.
Qed.

Definition sra_bit4__stmt : Prop := forall X, 0 <= X < 2^32 ->
  Z.shiftr (((Z.shiftl X 59 mod 2^64) + 2^63) mod 2^64 - 2^63) 63 = - ((X / 16) mod 2).
Section Sz2.
Variables X : ltac2:(SecDiet.SzSec.tyM 'sra_bit4__stmt "v" @X).
#[using="Type"] Lemma sra_bit4__body : ltac2:(SecDiet.SzSec.bodyP 'sra_bit4__stmt "v").
Proof.
  intros HX.
 rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  pose proof (bit4_decomp X ltac:(lia)) as D.
  pose proof (Z.mod_pos_bound X 16 ltac:(lia)) as R.
  pose proof (Z.mod_pos_bound (X / 16) 2 ltac:(lia)) as B.
  set (q := X / 32) in *. set (b := (X / 16) mod 2) in *. set (r := X mod 16) in *.
  rewrite D.
  replace ((32 * q + 16 * b + r) * 2 ^ 59) with (b * 2^63 + r * 2^59 + q * 2^64) by lia.
  rewrite Z.mod_add by lia.
  assert (b = 0 \/ b = 1) as [-> | ->] by lia.
  - rewrite (Z.mod_small (0 * 2^63 + r * 2^59)) by lia. rewrite Z.mod_small by lia.
    apply Z.div_small. lia.
  - replace (1 * 2 ^ 63 + r * 2 ^ 59) with (r * 2^59 + 2^63) by lia.
    rewrite (Z.mod_small (r * 2^59 + 2^63)) by lia.
    replace (r * 2 ^ 59 + 2 ^ 63 + 2 ^ 63) with (r * 2^59 + 1 * 2^64) by lia. rewrite Z.mod_add, Z.mod_small by lia.
    symmetry. apply Z.div_unique_pos with (r := r * 2^59); lia.
Qed.
End Sz2.
Lemma sra_bit4 : ltac:(let t := eval cbv delta [sra_bit4__stmt] in sra_bit4__stmt in exact t).
Proof. intros X. ltac2:(SecDiet.SzSec.closeP 'sra_bit4__body "v"). Qed.

Lemma testbit_16 : forall i, 0 <= i -> Z.testbit 16 i = (i =? 4).
Proof. intros i Hi. change 16 with (2^4). rewrite Z.pow2_bits_eqb by lia. apply Z.eqb_sym. Qed.
Definition land16_bit4__stmt : Prop := forall X, 0 <= X -> Z.land X 16 = 16 * ((X / 16) mod 2).
Section Sz4.
Variables X : ltac2:(SecDiet.SzSec.tyM 'land16_bit4__stmt "v" @X).
#[using="Type"] Lemma land16_bit4__body : ltac2:(SecDiet.SzSec.bodyP 'land16_bit4__stmt "v").
Proof.
  intros HX.
 pose proof (Z.mod_pos_bound (X / 16) 2 ltac:(lia)) as B.
  apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, testbit_16 by lia.
  assert ((X / 16) mod 2 = 0 \/ (X / 16) mod 2 = 1) as [E|E] by lia; rewrite E.
  - rewrite Z.mul_0_r, Z.bits_0. destruct (Z.eqb_spec i 4); [subst|apply andb_false_r].
    rewrite andb_true_r. apply Z.testbit_false; [lia|]. change (2^4) with 16. exact E.
  - rewrite Z.mul_1_r, testbit_16 by lia. destruct (Z.eqb_spec i 4); [subst|apply andb_false_r].
    rewrite andb_true_r. apply Z.testbit_true; [lia|]. change (2^4) with 16. exact E.
Qed.
End Sz4.
Lemma land16_bit4 : ltac:(let t := eval cbv delta [land16_bit4__stmt] in land16_bit4__stmt in exact t).
Proof. intros X. ltac2:(SecDiet.SzSec.closeP 'land16_bit4__body "v"). Qed.
(* [comment removed for export] *)
Lemma land_low32 : forall X k, 0 <= k < 2^32 -> Z.land (X mod 2^32) k = Z.land X k mod 2^32.
Proof.
  intros X k Hk. rewrite <- !Z.land_ones by lia.
  rewrite (Z.land_comm (Z.land X k)), Z.land_assoc, (Z.land_comm (Z.ones 32) X). reflexivity.
Qed.

Lemma CB_prefix_bytes_at' : forall m A n (bb : list byte) (p : list byte),
  rw_cells usegs m A [CB n bb] -> firstn (length p) bb = p -> bytes_at usegs m A p.
Proof.
  intros m A n bb p H E.
  pose proof (rw_cells_bytes_at _ _ _ _ H) as B. cbn [cells_bytes cbytes] in B. rewrite app_nil_r in B.
  rewrite <- E. rewrite <- (firstn_skipn (length p) bb) in B.
  exact (proj1 (proj1 (bytes_at_app _ _ _ _ _) B)).
Qed.
Lemma wfn_after_write' : forall f, wfn_of (f_after_write f) = F_STDIO_WRITE.
Proof. intros f. unfold wfn_of, f_after_write. destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; reflexivity. Qed.

Section Toread.
  Context {St : Type}.

  (* [comment removed for export] *)
  Definition tr_inv (f f' : file_st) : Prop :=
    f_fd f' = f_fd f /\ f_chan f' = f_chan f /\ f_bufsize f' = f_bufsize f /\ f_nord f' = f_nord f /\ f_nowr f' = f_nowr f /\ f_eof f' = f_eof f
    /\ f_wactive f' = false /\ f_wbuf f' = [] /\ f_rbuf f' = []
    /\ (f_stdoutw f' = true -> f_stdoutw f = true) /\ (f_lbf_nl f' = true -> f_lbf_nl f = true).

  Definition tr_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - TOREAD_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  Definition toread_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte)
      (lo : Z) (canary : word) (m : mem) : (bool * file_st) -> St -> machine_state -> Prop :=
    fun r st' ms' => st' = st /\ fst r = f_eof f /\ tr_inv f (snd r) /\ f_nord f = false /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (- Z.b2z (fst r))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch (tr_W sp Fp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' Fp (fcells flags (B + f_bufsize f) (B + f_bufsize f) closefn 0 0 0 readfn (wfn_of (snd r)) seekfn B (f_bufsize f) prev next (f_fd f) mode' (lbf_of (snd r)) tail)
      /\ ssp_cells m' canary.

  Section Tail.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis FLN : Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0).
    Hypothesis FLE : Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0).
    Hypothesis LO : lo <= bv_unsigned sp - TOREAD_DEPTH.
    Hypothesis GLO : 0x56000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis B0 : 0 < B.
    Hypothesis BShi : B + f_bufsize f <= 2^47.   (* [comment removed for export] *)
    Hypothesis BS0 : 0 <= f_bufsize f.

    (* [comment removed for export] *)
    Definition toread_tail__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells usegs m1 (bv_unsigned sp + -16) [C8 s0; C8 ra] ->
      rw_cells usegs m1 Fp (fcells flags 0 0 closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) \/
      (exists rp re, rw_cells usegs m1 Fp (fcells flags rp re closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail)) ->
      ssp_cells m1 canary -> stk usegs m1 lo (bv_unsigned sp + -16) -> mem_inv usegs m1 ->
      munch (tr_W sp Fp) m m1 -> wmono usegs m m1 ->
      tr_inv f (set_rbuf [] (set_w false [] f1)) ->
      implM usegs (let f2 := set_w false [] f1 in if f_nord f2 then munr else mret (f_eof f2, set_rbuf [] f2)) st
        (toread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TOREAD_TAIL) fc None m1 (seg_rom usegs)).
    Section Sz8.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'toread_tail__stmt "vvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma toread_tail__body : ltac2:(SecDiet.SzSec.bodyP 'toread_tail__stmt "vvvvvvvvvvvvvvvvvvvvvv").
    Proof using FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO. pin_using (fun (FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
 intros FR1 FC1 SSP1 ST1 MI1 MU1 WM1 INV.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (bv_unsigned_in_range 64 flags) as FLR. unfold bv_modulus in FLR. cbn in FLR.
      assert (FC : exists rp re, rw_cells usegs m1 Fp (fcells flags rp re closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail)).
      { destruct FC1 as [H | H]; [exists 0, 0; exact H | exact H]. }
      clear FC1. destruct FC as (rp & re & FC).
      pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      unfold fcells, file_cells in FC. unfold tr_W, TOREAD_DEPTH, TOREAD_TAIL in *. destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
      cbv zeta. cbn [f_nord f_eof set_w].
      pose proof INV as INV'. destruct INV as (If1 & If2 & If3 & If4 & If5 & If6 & _). cbn [set_rbuf set_w f_nord f_eof f_fd f_bufsize f_chan f_nowr] in If1, If2, If3, If4, If5, If6.
      rewrite If4, If6.
      apply implM_prefix.
      zs. zs.
      replace (Z.land (bv_unsigned (zx32 flags)) 4) with (if f_nord f then 4 else 0).
      2:{ unfold zx32. rewrite unsigned_lit by (pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
          rewrite land_low32 by lia. unfold F_NORD in FLN. rewrite FLN. destruct (f_nord f); reflexivity. }
      zs. zs. zs.
      destruct (f_nord f) eqn:NORD.
      { (* [comment removed for export] *) apply evt_done. apply implM_unr. }
      zs. if_false. zs. zs. zs. zs. zs. zs. zs.
      assert (X32 : bv_unsigned (zx32 flags) = bv_unsigned flags mod 2^32).
      { unfold zx32. apply unsigned_lit. pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)). lia. }
      assert (EB : (bv_unsigned (zx32 flags) / 16) mod 2 = Z.b2z (f_eof f)).
      { rewrite X32. pose proof (land16_bit4 (bv_unsigned flags mod 2^32) ltac:(apply Z.mod_pos_bound; lia)) as L.
        rewrite land_low32 in L by lia. unfold F_EOF in FLE. rewrite FLE in L.
        pose proof (Z.mod_pos_bound (bv_unsigned flags mod 2 ^ 32 / 16) 2 ltac:(lia)).
        destruct (f_eof f); cbn [Z.b2z]; [change (16 mod 2^32) with 16 in L | change (0 mod 2^32) with 0 in L]; lia. }
      replace (Z.shiftr (bv_signed (Z_to_bv 64 (Z.shiftl (bv_unsigned (zx32 flags)) 59))) 63) with (- Z.b2z (f_eof f)).
      2:{ rewrite Z_to_bv_signed. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus.
          change (2 ^ Z.of_N 64) with (2^64). change (2^64 `div` 2) with (2^63).
          rewrite <- (Zplus_mod_idemp_l (Z.shiftl (bv_unsigned (zx32 flags)) 59)).
          rewrite sra_bit4 by (rewrite X32; pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)); lia).
          rewrite EB. reflexivity. }
      zs. zs. zs. zs. zs.
      release_frame FR1 ST1 (bv_unsigned sp).
      apply evt_done. apply implM_ret. apply evt_done.
      unfold toread_post. cbn [fst snd]. split; [reflexivity|]. split; [reflexivity|]. split; [exact INV'|]. split; [exact NORD|].
      repeat (lazymatch goal with |- ex _ => eexists end).
      split; [cbv delta [mkR]; reflexivity|].
      split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
      split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz8.
    Lemma toread_tail : ltac:(let t := eval cbv delta [toread_tail__stmt] in toread_tail__stmt in exact t).
    Proof using FLE FLN FPLO FSEP1 FSEP2 Fp0 GLO LO. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'toread_tail__body "vvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End Tail.

  Lemma implM_retb : forall {A B} (a : A) (k : A -> M St B) (s : St) Q ms,
    implM usegs (k a) s Q ms -> implM usegs (mbind (mret a) k) s Q ms.
  Proof using Type. pin_using tt. intros A B a k s Q ms H. exact H. Qed.

  Definition toread_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rpos rend closefn readfn seekfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (lo : Z) (canary : word),
      rw_cells usegs m Fp (fcells flags rpos rend closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) seekfn B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_NORD = (if f_nord f then F_NORD else 0) ->
      Z.land (bv_unsigned flags) F_EOF = (if f_eof f then F_EOF else 0) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> f_rbuf f = [] ->
      a0 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - TOREAD_DEPTH -> 0x56000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv usegs m ->
      0 <= Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      implM usegs (toread f) st
        (toread_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 TOREAD) fc None m (seg_rom usegs)).
  Section Sz10.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'toread_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma toread_spec__body : ltac2:(SecDiet.SzSec.bodyP 'toread_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros FC FLN FLE FL64 BUF BUFP WB0 RB0 -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BShi BS0 WBL BSZ SEPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold TOREAD, TOREAD_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (tr_W sp Fp) m) as MU. pose proof (wmono_refl usegs m) as WM. unfold tr_W, TOREAD_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'.
    assert (TRI : forall f1, f_fd f1 = f_fd f -> f_chan f1 = f_chan f -> f_bufsize f1 = f_bufsize f -> f_nord f1 = f_nord f -> f_nowr f1 = f_nowr f -> f_eof f1 = f_eof f ->
                  (f_stdoutw f1 = true -> f_stdoutw f = true) -> (f_lbf_nl f1 = true -> f_lbf_nl f = true) -> tr_inv f (set_rbuf [] (set_w false [] f1))).
    { intros f1 E1 E2 E3 E4 E5 E6 E7 E8. unfold tr_inv. cbn. repeat split; auto. }
    unfold toread.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      apply implM_prefix.
      carve_frame 16%nat ST.
      do 10 zs. zs.
      if_true.
      apply evt_done.
      eapply toread_tail with (f1 := f); fastfirst (first
        [ noevar_assumption | exact FLN | exact FLE | exact FR | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD] | exact MI | exact MU | exact WM
        | right; eexists _, _; unfold fcells, file_cells; exact FC
        | apply TRI; auto
        | split; assumption | assumption | lia
        ]).
    - (* [comment removed for export] *)
      replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
        by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
      assert (WACT : f_wactive f = true).
      { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
      rewrite WACT in FC.
      assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
      unfold fcells, file_cells in FC.
      change (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
      apply implM_prefix.
      carve_frame 16%nat ST.
      do 10 zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evt_done.
      unfold boxed in BUF.
      assert (BUFB : bytes_at usegs m0 B (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP].
        eapply (rw_cells_transport usegs _ m m0); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      eapply implM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rpos) (rend := rend) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
          (seekfn := seekfn) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: fastfirst (first [ noevar_assumption | reflexivity | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                   | apply bytes_at_nil; lia
                   | generalize CH; destruct (f_chan f); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; cbn; lia]]
                   | left; reflexivity
                   | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia
                   | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                   ]). }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x1b5e8)) with (Z_to_bv 64 0x1b5e8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -16) [C8 s0; C8 ra]).
      { eapply (rw_cells_transport usegs _ m0 m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      eapply toread_tail with (f1 := f_after_write f); fastfirst (first
        [ noevar_assumption | exact FLN | exact FLE | exact FR2 | exact SSP2 | exact MI2 | exact ST2
        | apply (munch_trans _ m m0 m2); [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp, tr_W, TOREAD_DEPTH; cbn [outside]; intros; lia]
        | eapply wmono_trans; [exact WM | exact WM2]
        | right; eexists _, _; rewrite wfn_after_write'; exact FC2
        | apply TRI; unfold f_after_write; destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; auto; intros HH; discriminate HH
        | assumption | lia
        ]).
  Qed.
  End Sz10.
  Theorem toread_spec : ltac:(let t := eval cbv delta [toread_spec__stmt] in toread_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rpos rend closefn readfn seekfn B prev next mode tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'toread_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Toread.
End TwB.
End F_toread.

(* [comment removed for export] *)
Module F_fflush.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FFLUSH : Z := 0x1ac78.
Definition FF_SYNC : Z := 0x1acf4.
Definition FFLUSH_DEPTH : Z := 176.   (* [comment removed for export] *)

Lemma rbuf_after_write' : forall f, f_rbuf (f_after_write f) = f_rbuf f.
Proof. intros f. unfold f_after_write. destruct (f_stdoutw f); reflexivity. Qed.

Section Fflush.
  Context {St : Type}.

  Definition ff_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - FFLUSH_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  Definition fflush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte)
      (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ tr_inv f f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom ssegs)
      /\ munch (ff_W sp Fp) m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
      /\ stk ssegs m' lo (bv_unsigned sp)
      /\ rw_cells ssegs m' Fp (fcells flags 0 0 closefn 0 0 0 readfn (wfn_of f') seekfn B (f_bufsize f) prev next (f_fd f) mode' (lbf_of f') tail)
      /\ ssp_cells m' canary.

  Lemma implM_sys_tt_ret : forall {A B} (n : M St A) (X : B) s (Q : B -> St -> machine_state -> Prop) ms,
    implM ssegs n s (fun _ s' ms' => evt ssegs (Q X s') ms') ms ->
    implM ssegs (mbind (mbind n (fun _ => mret tt)) (fun _ => mret X)) s Q ms.
  Proof using Type. pin_using tt.
    intros A B n X s Q ms H. eapply implM_bind with (Q1 := fun _ s' ms' => evt ssegs (Q X s') ms').
    - eapply implM_bind with (Q1 := fun _ s' ms' => evt ssegs (Q X s') ms'); [exact H|].
      intros a s' ms' H'. apply implM_ret. apply evt_done. exact H'.
    - intros a s' ms' H'. apply implM_ret. exact H'.
  Qed.

  Section Sync.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis LO : lo <= bv_unsigned sp - FFLUSH_DEPTH.
    Hypothesis GLO : 0x55000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis FD : f_chan f = false -> 3 <= f_fd f < 2^31.

    (* [comment removed for export] *)
    Definition ff_sync__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (rp wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells ssegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells ssegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f1)) closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) ->
      (f_rbuf f1 <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f1) < 2^63 -> seekfn = F_STDIO_SEEK ->
      ssp_cells m1 canary -> stk ssegs m1 lo (bv_unsigned sp + -32) -> mem_inv ssegs m1 ->
      munch (ff_W sp Fp) m m1 -> wmono ssegs m m1 ->
      tr_inv f (set_rbuf [] (set_w false [] f1)) ->
      implM ssegs (sync_read_pos f1 ;;; mret (set_rbuf [] (set_w false [] f1))) st
        (fflush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 Fp) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FF_SYNC) fc None m1 (seg_rom ssegs)).
    Section Sz3.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'ff_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma ff_sync__body : ltac2:(SecDiet.SzSec.bodyP 'ff_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO. pin_using (fun (FD FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
      intros FR1 FC1 RCH RP0 RPHI SEEK SSP1 ST1 MI1 MU1 WM1 INV.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold ff_W, FFLUSH_DEPTH, FF_SYNC in *.
      destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
      pose proof INV as INV'. destruct INV as (If1 & If2 & If3 & _).
      cbn [set_rbuf set_w f_fd f_chan f_bufsize] in If1, If2, If3.
      unfold sync_read_pos. unfold zlength in *.
      assert (CASES : f_rbuf f1 = [] \/ f_rbuf f1 <> []) by (destruct (f_rbuf f1); [left; reflexivity | right; discriminate]).
      destruct CASES as [RB | RB].
      - (* [comment removed for export] *)
        rewrite RB. apply implM_retb. apply implM_ret.
        rewrite RB in FC. change (Z.of_nat (@length Z [])) with 0 in FC. rewrite Z.add_0_r in FC.
        zs. zs. zs. if_true.
        do 6 zs. zs. if_true. zs. do 6 zs.
        release_frame FR1 ST1 (bv_unsigned sp).
        apply evt_done. unfold fflush_post. split; [reflexivity|]. split; [exact INV'|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
      - (* [comment removed for export] *)
        replace (match f_rbuf f1 with [] => mret tt | _ :: _ => (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt) end : M St unit)
          with (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt : M St unit)
          by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | reflexivity]).
        assert (NB1 : 1 <= Z.of_nat (length (f_rbuf f1))) by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | cbn; lia]).
        specialize (RCH RB). specialize (FD RCH).
        apply implM_prefix.
        zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
        zs. zs. zs. zs. rewrite SEEK in *. unfold F_STDIO_SEEK in *. zs.
        apply evt_done.
        apply implM_sys_tt_ret. rewrite If1.
        eapply implM_post_evt.
        { eapply (stdio_seek_spec (St:=St)) with (fd := f_fd f) (off := - Z.of_nat (length (f_rbuf f1))) (whence := 1);
            fastfirst (first [ noevar_assumption | exact FC | reflexivity | f_equal; lia | exact MI1 | lia ]). }
        cbv beta. intros r st2 ms2 (-> & PO). destruct_exs PO. subst ms2.
        replace (ret_pc (Z_to_bv 64 0x1ad14)) with (Z_to_bv 64 0x1ad14 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        do 6 zs. zs. if_true. zs. do 6 zs.
        release_frame FR1 ST1 (bv_unsigned sp).
        apply evt_done. apply evt_done. unfold fflush_post. split; [reflexivity|]. split; [exact INV'|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz3.
    Lemma ff_sync : ltac:(let t := eval cbv delta [ff_sync__stmt] in ff_sync__stmt in exact t).
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'ff_sync__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End Sync.

  Definition fflush_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rp closefn readfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (lo : Z) (canary : word),
      rw_cells ssegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> (f_rbuf f <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f) < 2^63 ->
      a0 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk ssegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FFLUSH_DEPTH -> 0x55000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv ssegs m ->
      0 < Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      implM ssegs (fflush_file f) st
        (fflush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn F_STDIO_SEEK B prev next tail lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FFLUSH) fc None m (seg_rom ssegs)).
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn B prev next mode tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'fflush_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fflush_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fflush_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
    intros FC FL64 BUF BUFP WB0 RCH RP0 RPHI -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BShi BS0 WBL BSZ SEPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FFLUSH, FFLUSH_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (ff_W sp Fp) m) as MU. pose proof (wmono_refl ssegs m) as WM. unfold ff_W, FFLUSH_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'.
    assert (FD : f_chan f = false -> 3 <= f_fd f < 2^31) by (intros E; rewrite E in CH; exact CH).
    assert (TRI : forall f1, f_fd f1 = f_fd f -> f_chan f1 = f_chan f -> f_bufsize f1 = f_bufsize f -> f_nord f1 = f_nord f -> f_nowr f1 = f_nowr f -> f_eof f1 = f_eof f ->
                  (f_stdoutw f1 = true -> f_stdoutw f = true) -> (f_lbf_nl f1 = true -> f_lbf_nl f = true) -> tr_inv f (set_rbuf [] (set_w false [] f1))).
    { intros f1 E1 E2 E3 E4 E5 E6 E7 E8. unfold tr_inv. cbn. repeat split; auto. }
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold fflush_file.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      apply implM_prefix.
      carve_frame 32%nat ST.
      do 5 zs. zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. zs. if_true.
      apply evt_done.
      eapply ff_sync with (f1 := f); fastfirst (first
        [ noevar_assumption | exact FR | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD] | exact MI | exact MU | exact WM | exact RCH | exact FD
        | unfold fcells, file_cells; exact FC
        | apply TRI; auto
        | reflexivity | assumption | lia
        ]).
    - (* [comment removed for export] *)
      replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
        by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
      assert (WACT : f_wactive f = true).
      { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
      rewrite WACT in FC.
      assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
      unfold fcells, file_cells in FC.
      change (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells ssegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
      apply implM_prefix.
      carve_frame 32%nat ST.
      do 5 zs. zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evt_done.
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
      unfold boxed in BUF.
      assert (BUFB : bytes_at ssegs mA B (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP].
        eapply (rw_cells_transport ssegs _ m mA); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      eapply implM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf f)) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
          (seekfn := F_STDIO_SEEK) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: fastfirst (first [ noevar_assumption | reflexivity | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                   | apply bytes_at_nil; lia
                   | generalize CH; destruct (f_chan f); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; cbn; lia]]
                   | left; reflexivity
                   | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia
                   | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                   ]). }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x1acec)) with (Z_to_bv 64 0x1acec : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR2 : rw_cells ssegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (rw_cells_transport ssegs _ mA m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
      apply implM_prefix. zs. zs. if_cases Hw; zify_cond Hw. 1:{ exfalso. rewrite ?Z.mod_small in Hw by lia. lia. }
      apply evt_done.
      eapply ff_sync with (f1 := f_after_write f) (rp := rp); rewrite ?rbuf_after_write'; fastfirst (first
        [ noevar_assumption | exact FR2 | exact SSP2 | exact MI2 | exact ST2 | exact RCH | exact FD
        | apply (munch_trans _ m mA m2); [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp, ff_W, FFLUSH_DEPTH; cbn [outside]; intros; lia]
        | eapply wmono_trans; [exact WM | exact WM2]
        | rewrite wfn_after_write'; exact FC2
        | apply TRI; unfold f_after_write; destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; auto; intros HH; discriminate HH
        | reflexivity | assumption | lia
        ]).
  Qed.
  End Sz4.
  Theorem fflush_spec : ltac:(let t := eval cbv delta [fflush_spec__stmt] in fflush_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn B prev next mode tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'fflush_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fflush.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_towrite.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_toread.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FFLUSH : Z := 0x1b438.
Definition FF_SYNC : Z := 0x1b4b4.
Definition FFLUSH_DEPTH : Z := 176.   (* [comment removed for export] *)

Lemma rbuf_after_write' : forall f, f_rbuf (f_after_write f) = f_rbuf f.
Proof. intros f. unfold f_after_write. destruct (f_stdoutw f); reflexivity. Qed.

Section Fflush.
  Context {St : Type}.

  Definition ff_W (sp : word) (Fp : Z) : list (Z * Z) := [(bv_unsigned sp - FFLUSH_DEPTH, bv_unsigned sp); (Fp, Fp + 232)].

  Definition fflush_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte)
      (lo : Z) (canary : word) (m : mem) : file_st -> St -> machine_state -> Prop :=
    fun f' st' ms' => st' = st /\ tr_inv f f' /\
      exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mode' : word) (m' : mem),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ munch (ff_W sp Fp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
      /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' Fp (fcells flags 0 0 closefn 0 0 0 readfn (wfn_of f') seekfn B (f_bufsize f) prev next (f_fd f) mode' (lbf_of f') tail)
      /\ ssp_cells m' canary.

  Lemma implM_sys_tt_ret : forall {A B} (n : M St A) (X : B) s (Q : B -> St -> machine_state -> Prop) ms,
    implM usegs n s (fun _ s' ms' => evt usegs (Q X s') ms') ms ->
    implM usegs (mbind (mbind n (fun _ => mret tt)) (fun _ => mret X)) s Q ms.
  Proof using Type. pin_using tt.
    intros A B n X s Q ms H. eapply implM_bind with (Q1 := fun _ s' ms' => evt usegs (Q X s') ms').
    - eapply implM_bind with (Q1 := fun _ s' ms' => evt usegs (Q X s') ms'); [exact H|].
      intros a s' ms' H'. apply implM_ret. apply evt_done. exact H'.
    - intros a s' ms' H'. apply implM_ret. exact H'.
  Qed.

  Section Sync.
    Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
    Variables (f : file_st) (st : St) (Fp : Z) (flags : word) (closefn readfn seekfn B prev next : Z) (tail : list byte) (lo : Z) (canary : word) (m : mem).
    Hypothesis LO : lo <= bv_unsigned sp - FFLUSH_DEPTH.
    Hypothesis GLO : 0x56000 <= lo.
    Hypothesis Fp0 : 0 <= Fp.
    Hypothesis FPLO : Fp + 232 <= lo.
    Hypothesis FSEP1 : Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp.
    Hypothesis FSEP2 : Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp.
    Hypothesis FD : f_chan f = false -> 3 <= f_fd f < 2^31.

    (* [comment removed for export] *)
    Definition ff_sync__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (f1 : file_st) (mode1 : word) (rp wend1 wpos1 wbase1 : Z) (m1 : mem),
      rw_cells usegs m1 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells usegs m1 Fp (fcells flags rp (rp + zlength (f_rbuf f1)) closefn wend1 wpos1 wbase1 readfn (wfn_of f1) seekfn B (f_bufsize f) prev next (f_fd f) mode1 (lbf_of f1) tail) ->
      (f_rbuf f1 <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f1) < 2^63 -> seekfn = F_STDIO_SEEK ->
      ssp_cells m1 canary -> stk usegs m1 lo (bv_unsigned sp + -32) -> mem_inv usegs m1 ->
      munch (ff_W sp Fp) m m1 -> wmono usegs m m1 ->
      tr_inv f (set_rbuf [] (set_w false [] f1)) ->
      implM usegs (sync_read_pos f1 ;;; mret (set_rbuf [] (set_w false [] f1))) st
        (fflush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn seekfn B prev next tail lo canary m)
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 s0 (Z_to_bv 64 Fp) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FF_SYNC) fc None m1 (seg_rom usegs)).
    Section Sz3.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1 : ltac2:(SecDiet.SzSec.tyM 'ff_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv" @x1).
    Lemma ff_sync__body : ltac2:(SecDiet.SzSec.bodyP 'ff_sync__stmt "vvvvvvvvvvvvvvvvvvvvvvv").
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO. pin_using (fun (FD FPLO FSEP1 FSEP2 Fp0 GLO LO : unit) => tt).
 intros FR1 FC1 RCH RP0 RPHI SEEK SSP1 ST1 MI1 MU1 WM1 INV.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (rw_cells_bound _ _ _ _ FC1) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
      pose proof FC1 as FC. unfold fcells, file_cells in FC. unfold ff_W, FFLUSH_DEPTH, FF_SYNC in *.
      destruct SSP1 as [GOT GUARD]. unfold got_ssp, ssp_guard in *.
      pose proof INV as INV'. destruct INV as (If1 & If2 & If3 & _).
      cbn [set_rbuf set_w f_fd f_chan f_bufsize] in If1, If2, If3.
      unfold sync_read_pos. unfold zlength in *.
      assert (CASES : f_rbuf f1 = [] \/ f_rbuf f1 <> []) by (destruct (f_rbuf f1); [left; reflexivity | right; discriminate]).
      destruct CASES as [RB | RB].
      - (* [comment removed for export] *)
        rewrite RB. apply implM_retb. apply implM_ret.
        rewrite RB in FC. change (Z.of_nat (@length Z [])) with 0 in FC. rewrite Z.add_0_r in FC.
        zs. zs. zs. if_true.
        do 6 zs. zs. if_true. zs. do 6 zs.
        release_frame FR1 ST1 (bv_unsigned sp).
        apply evt_done. unfold fflush_post. split; [reflexivity|]. split; [exact INV'|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
      - (* [comment removed for export] *)
        replace (match f_rbuf f1 with [] => mret tt | _ :: _ => (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt) end : M St unit)
          with (_ <- msys (NLseek (f_fd f1) (- Z.of_nat (length (f_rbuf f1))) SEEK_CUR) dec_lseek_ok ;; mret tt : M St unit)
          by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | reflexivity]).
        assert (NB1 : 1 <= Z.of_nat (length (f_rbuf f1))) by (destruct (f_rbuf f1); [exfalso; exact (RB eq_refl) | cbn; lia]).
        specialize (RCH RB). specialize (FD RCH).
        apply implM_prefix.
        zs. zs. zs. if_cases Hr; zify_cond Hr. 1:{ exfalso. rewrite ?Z.mod_small in Hr by lia. lia. }
        zs. zs. zs. zs. rewrite SEEK in *. unfold F_STDIO_SEEK in *. zs.
        apply evt_done.
        apply implM_sys_tt_ret. rewrite If1.
        eapply implM_post_evt.
        { eapply (stdio_seek_spec (St:=St)) with (fd := f_fd f) (off := - Z.of_nat (length (f_rbuf f1))) (whence := 1);
            fastfirst (first [ noevar_assumption | exact FC | reflexivity | f_equal; lia | exact MI1 | lia ]). }
        cbv beta. intros r st2 ms2 (-> & PO). destruct_exs PO. subst ms2.
        replace (ret_pc (Z_to_bv 64 0x1b4d4)) with (Z_to_bv 64 0x1b4d4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
        do 6 zs. zs. if_true. zs. do 6 zs.
        release_frame FR1 ST1 (bv_unsigned sp).
        apply evt_done. apply evt_done. unfold fflush_post. split; [reflexivity|]. split; [exact INV'|].
        repeat (lazymatch goal with |- ex _ => eexists end).
        split; [cbv delta [mkR]; reflexivity|].
        split; [exact MU1|]. split; [exact WM1|]. split; [exact MI1|]. split; [exact ST1|].
        split; [unfold fcells, file_cells; exact FC|]. split; [exact GOT | exact GUARD].
    Qed.
    End Sz3.
    Lemma ff_sync : ltac:(let t := eval cbv delta [ff_sync__stmt] in ff_sync__stmt in exact t).
    Proof using FD FPLO FSEP1 FSEP2 Fp0 GLO LO. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 f1 mode1 rp wend1 wpos1 wbase1 m1. ltac2:(SecDiet.SzSec.closeP 'ff_sync__body "vvvvvvvvvvvvvvvvvvvvvvv"). Qed.
  End Sync.

  Definition fflush_spec__stmt : Prop := forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (st : St)
           (f : file_st) (Fp : Z) (flags : word) (rp closefn readfn B prev next : Z)
           (mode : word) (tail : list byte) (bufbytes : list byte) (lo : Z) (canary : word),
      rw_cells usegs m Fp (fcells flags rp (rp + zlength (f_rbuf f)) closefn
                             (if f_wactive f then B + f_bufsize f else 0) (if f_wactive f then B + zlength (f_wbuf f) else 0) (if f_wactive f then B else 0)
                             readfn (wfn_of f) F_STDIO_SEEK B (f_bufsize f) prev next (f_fd f) mode (lbf_of f) tail) ->
      Z.land (bv_unsigned flags) F_SVB = 0 ->
      rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes] -> firstn (length (f_wbuf f)) bufbytes = to_bytes (f_wbuf f) ->
      (f_wactive f = false -> f_wbuf f = []) -> (f_rbuf f <> [] -> f_chan f = false) -> 0 <= rp -> rp + zlength (f_rbuf f) < 2^63 ->
      a0 = Z_to_bv 64 Fp ->
      (if f_chan f then (f_fd f = 1 \/ f_fd f = 2) else (3 <= f_fd f < 2^31)) ->
      stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - FFLUSH_DEPTH -> 0x56000 <= lo ->
      bv_unsigned sp <= 2^47 ->   (* [comment removed for export] *)
      ssp_cells m canary -> mem_inv usegs m ->
      0 < Fp -> Fp + 232 <= lo ->
      (Fp + 232 <= got_ssp \/ got_ssp + 8 <= Fp) -> (Fp + 232 <= ssp_guard \/ ssp_guard + 8 <= Fp) ->
      0 < B -> B + f_bufsize f <= 2^47 (* [comment removed for export] *) -> 0 <= f_bufsize f -> zlength (f_wbuf f) <= f_bufsize f -> f_bufsize f <= 2^25 ->
      (B + f_bufsize f <= lo \/ bv_unsigned sp <= B) /\ (B + f_bufsize f <= Fp \/ Fp + 232 <= B) ->
      implM usegs (fflush_file f) st
        (fflush_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc f st Fp flags closefn readfn F_STDIO_SEEK B prev next tail lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 FFLUSH) fc None m (seg_rom usegs)).
  Section Sz4.
  Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn B prev next mode tail bufbytes lo canary : ltac2:(SecDiet.SzSec.tyM 'fflush_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
  Lemma fflush_spec__body : ltac2:(SecDiet.SzSec.bodyP 'fflush_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros FC FL64 BUF BUFP WB0 RCH RP0 RPHI -> CH ST LO GLO SP47 SSP MI Fp0 FPLO FSEP1 FSEP2 B0 BShi BS0 WBL BSZ SEPB.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof SSP as SSP0. destruct SSP as [GOT GUARD]. unfold got_ssp, ssp_guard in *. unfold FFLUSH, FFLUSH_DEPTH in *.
    pose proof (rw_cells_bound _ _ _ _ FC) as FB. unfold fcells in FB. rewrite file_cells_size in FB.
    pose proof (munch_refl (ff_W sp Fp) m) as MU. pose proof (wmono_refl usegs m) as WM. unfold ff_W, FFLUSH_DEPTH in MU.
    pose proof WBL as WBL'. unfold zlength in WBL'.
    assert (FD : f_chan f = false -> 3 <= f_fd f < 2^31) by (intros E; rewrite E in CH; exact CH).
    assert (TRI : forall f1, f_fd f1 = f_fd f -> f_chan f1 = f_chan f -> f_bufsize f1 = f_bufsize f -> f_nord f1 = f_nord f -> f_nowr f1 = f_nowr f -> f_eof f1 = f_eof f ->
                  (f_stdoutw f1 = true -> f_stdoutw f = true) -> (f_lbf_nl f1 = true -> f_lbf_nl f = true) -> tr_inv f (set_rbuf [] (set_w false [] f1))).
    { intros f1 E1 E2 E3 E4 E5 E6 E7 E8. unfold tr_inv. cbn. repeat split; auto. }
    assert (LCK : 9223372036854775808 <= bv_unsigned (sx32 (Z_to_bv 64 4294967295))) by (vm_compute; discriminate).
    unfold fflush_file.
    assert (CASES : f_wbuf f = [] \/ f_wbuf f <> []) by (destruct (f_wbuf f); [left; reflexivity | right; discriminate]).
    destruct CASES as [WBN | WBN].
    - (* [comment removed for export] *)
      rewrite WBN. apply implM_retb.
      unfold fcells, file_cells in FC. rewrite WBN in FC. change (zlength []) with 0 in FC. rewrite Z.add_0_r in FC.
      apply implM_prefix.
      carve_frame 32%nat ST.
      do 5 zs. zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. zs. if_true.
      apply evt_done.
      eapply ff_sync with (f1 := f); fastfirst (first
        [ noevar_assumption | exact FR | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD] | exact MI | exact MU | exact WM | exact RCH | exact FD
        | unfold fcells, file_cells; exact FC
        | apply TRI; auto
        | reflexivity | assumption | lia
        ]).
    - (* [comment removed for export] *)
      replace (match f_wbuf f with [] => mret f | _ :: _ => file_writefn f [] end) with (file_writefn (St:=St) f [])
        by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | reflexivity]).
      assert (WACT : f_wactive f = true).
      { destruct (f_wactive f) eqn:E; [reflexivity | exfalso; exact (WBN (WB0 eq_refl))]. }
      rewrite WACT in FC.
      assert (NB1 : 1 <= zlength (f_wbuf f)) by (destruct (f_wbuf f); [exfalso; exact (WBN eq_refl) | unfold zlength; cbn; lia]).
      unfold fcells, file_cells in FC.
      change (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes]) with (boxed (rw_cells usegs m B [CB (Z.to_nat (f_bufsize f)) bufbytes])) in BUF.
      apply implM_prefix.
      carve_frame 32%nat ST.
      do 5 zs. zs. if_cases Hz; zify_cond Hz. 1:{ exfalso. rewrite ?Z.mod_small in Hz by lia. lia. }
      zs. zs. zs. if_cases Hl; zify_cond Hl. 2:{ exfalso. lia. }
      zs. zs. zs. zs. if_cases Hb; zify_cond Hb. 1:{ exfalso. unfold zlength in *. rewrite ?Z.mod_small in Hb by lia. lia. }
      zs. zs. zs. zs.
      assert (WFR : 0 <= wfn_of f < 2^64 /\ wfn_of f mod 2 = 0) by (unfold wfn_of, F_STDOUT_WRITE, F_STDIO_WRITE; destruct (f_stdoutw f); cbn; lia).
      zs. rewrite (ret_pc_even (wfn_of f)) by lia.
      apply evt_done.
      lazymatch goal with |- implM _ _ _ _ (MS _ _ _ _ _ ?mm _) => rename mm into mA end.
      unfold boxed in BUF.
      assert (BUFB : bytes_at usegs mA B (to_bytes (f_wbuf f))).
      { eapply CB_prefix_bytes_at' with (n := Z.to_nat (f_bufsize f)) (bb := bufbytes); [| rewrite length_to_bytes; exact BUFP].
        eapply (rw_cells_transport usegs _ m mA); [exact BUF | exact MU | exact WM | cbn [disjoint_from cells_size csize Nat.add]; destruct SEPB as [SB1 SB2]; lia]. }
      eapply implM_bind.
      { eapply (file_writefn_spec (St:=St)) with (f := f) (s := []) (S := 0) (lo := lo) (canary := canary)
          (Fp := Fp) (flags := flags) (rpos := rp) (rend := rp + zlength (f_rbuf f)) (closefn := closefn) (wend := B + f_bufsize f) (readfn := readfn)
          (seekfn := F_STDIO_SEEK) (B := B) (bufsize := f_bufsize f) (prev := prev) (next := next) (mode := _) (tail := tail);
          rewrite ?unsigned_lit by lia.
        all: fastfirst (first [ noevar_assumption | reflexivity | exact FC | exact ST | exact MI | exact BUFB | exact FL64 | unfold ssp_cells, got_ssp, ssp_guard; split; [exact GOT | exact GUARD]
                   | apply bytes_at_nil; lia
                   | generalize CH; destruct (f_chan f); intros CHx; [exact CHx | split; [exact CHx | unfold zlength in *; cbn; lia]]
                   | left; reflexivity
                   | destruct SEPB as [SB1 SB2]; unfold zlength in *; split; lia
                   | unfold zlength in *; cbn [length Z.of_nat]; lia | unfold WRITEFN_DEPTH; lia | unfold got_ssp, ssp_guard in *; lia
                   ]). }
      cbv beta. intros f1 st1 ms1 (-> & -> & PO). destruct_exs PO.
      destruct PO as (-> & MU2 & WM2 & MI2 & ST2 & FC2 & SSP2).
      lazymatch type of MI2 with mem_inv _ ?mm => rename mm into m2 end.
      unfold wf_W, WRITEFN_DEPTH in MU2. rewrite !unsigned_lit in MU2, ST2 by lia.
      replace (ret_pc (Z_to_bv 64 0x1b4ac)) with (Z_to_bv 64 0x1b4ac : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (FR2 : rw_cells usegs m2 (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra]).
      { eapply (rw_cells_transport usegs _ mA m2); [exact FR | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Nat.add]; lia]. }
      pose proof FC2 as FC2c. unfold fcells, file_cells in FC2c.
      apply implM_prefix. zs. zs. if_cases Hw; zify_cond Hw. 1:{ exfalso. rewrite ?Z.mod_small in Hw by lia. lia. }
      apply evt_done.
      eapply ff_sync with (f1 := f_after_write f) (rp := rp); rewrite ?rbuf_after_write'; fastfirst (first
        [ noevar_assumption | exact FR2 | exact SSP2 | exact MI2 | exact ST2 | exact RCH | exact FD
        | apply (munch_trans _ m mA m2); [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp, ff_W, FFLUSH_DEPTH; cbn [outside]; intros; lia]
        | eapply wmono_trans; [exact WM | exact WM2]
        | rewrite wfn_after_write'; exact FC2
        | apply TRI; unfold f_after_write; destruct (f_stdoutw f) eqn:E; cbn; rewrite ?E; auto; intros HH; discriminate HH
        | reflexivity | assumption | lia
        ]).
  Qed.
  End Sz4.
  Theorem fflush_spec : ltac:(let t := eval cbv delta [fflush_spec__stmt] in fflush_spec__stmt in exact t).
  Proof using Type. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st f Fp flags rp closefn readfn B prev next mode tail bufbytes lo canary. ltac2:(SecDiet.SzSec.closeP 'fflush_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.
End Fflush.
End TwB.
End F_fflush.

(* [comment removed for export] *)
Module F_fclose.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad StdioCore. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require InitMem. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require Exit__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FCLOSE : Z := 0x1ab54.
Definition FCLOSE_FREE_RA : Z := 0x1ac00.    (* [comment removed for export] *)
Definition FREE_ENTRY' : Z := 0x1878c.
Local Ltac mi := match goal with H : mem_inv ssegs _ |- _ => exact H end.

(* [comment removed for export] *)
Lemma free_null : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  evt ssegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom ssegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREE_ENTRY') fc None m (seg_rom ssegs)).
Proof. intros. unfold FREE_ENTRY'. step. step. if_true. step. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
Definition fclose_cells (flags : word) (closefn readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C1 (Z_to_bv 8 (bv_unsigned flags)); CB 3 (List.tl (le4 flags)); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 closefn);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 readfn); C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn);
   C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 prev); C8 (Z_to_bv 64 next);
   C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 16 (firstn 16 tail); C8 (Z_to_bv 64 0); CB 56 (skipn 24 tail)].

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. reflexivity. Qed.

Lemma tail_split : forall (tail : list byte),
  firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
  firstn 16 tail ++ (repeat (Z_to_bv 8 0) 8 ++ skipn 24 tail) = tail.
Proof.
  intros tail GL. rewrite <- GL.
  replace (skipn 24 tail) with (skipn 8 (skipn 16 tail)) by (rewrite skipn_skipn; reflexivity).
  rewrite (firstn_skipn 8 (skipn 16 tail)). apply firstn_skipn.
Qed.

Lemma file_cells_tail_length : forall m Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  rw_cells ssegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  length tail = 80%nat.
Proof.
  intros until tail. intros [[WF _] _]. unfold file_cells in WF. cbn [cells_wf cell_wf] in WF.
  repeat match type of WF with _ /\ _ => let X := fresh "X" in destruct WF as [X WF] end.
  assumption.
Qed.

Lemma fclose_cells_recast : forall m Fp flags closefn readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  rw_cells ssegs m Fp (file_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
  rw_cells ssegs m Fp (fclose_cells flags closefn readfn writefn seekfn buf bufsize prev next fd mode lbf tail).
Proof.
  intros until tail. intros FC GL.
  pose proof (file_cells_tail_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC) as TL.
  eapply rw_cells_recast; [exact FC| | |].
  - unfold fclose_cells. cbn -[skipn firstn]. rewrite length_firstn, length_skipn. repeat split; try reflexivity; lia.
  - unfold fclose_cells, file_cells. cbn -[skipn firstn le8 Z.shiftr repeat].
    rewrite le8_zero. rewrite !app_nil_r. rewrite (tail_split tail GL). reflexivity.
  - reflexivity.
Qed.

Section Fclose.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp lo : Z).
  Hypothesis LO : lo <= bv_unsigned sp - 512.
  Hypothesis GLO : 0x55000 <= lo.
  Hypothesis Fp0 : 0 < Fp.
  Hypothesis FPLO : Fp + 1264 <= lo.
  Hypothesis FPST : Fp + 1264 <= 0x10000 \/ 0x55000 <= Fp.

  (* [comment removed for export] *)
  Lemma fclose_S1 : forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    stk ssegs m lo (bv_unsigned sp) -> mem_inv ssegs m ->
    evt ssegs (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR (Z_to_bv 64 0x1ab74) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 FFLUSH) fc None m1 (seg_rom ssegs)
        /\ rw_cells ssegs m1 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
        /\ stk ssegs m1 lo (bv_unsigned sp + -48))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FCLOSE) fc None m (seg_rom ssegs)).
  Proof using LO. pin_using (fun (LO : unit) => tt).
    intros until m. intros ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold FCLOSE, FFLUSH.
    carve_frame 48%nat ST.
    do 6 zs. zs. zs.
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.

  (* [comment removed for export] *)
  Lemma fclose_S2 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (mm : mem)
      (flags mode : word) (readfn writefn buf bufsize prev next fd lbf : Z) (tail : list byte),
    rw_cells ssegs mm Fp (fcells flags 0 0 F_STDIO_CLOSE 0 0 0 readfn writefn F_STDIO_SEEK buf bufsize prev next fd mode lbf tail) ->
    mem_inv ssegs mm ->
    evt ssegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1ab9c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) a0
                                         (Z_to_bv 64 Fp) (Z_to_bv 64 F_STDIO_CLOSE) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 STDIO_CLOSE) fc None mm (seg_rom ssegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ab74) fc None mm (seg_rom ssegs)).
  Proof using Type. pin_using tt.
    intros until tail. intros FC MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    pose proof FC as FC'. unfold fcells, file_cells, F_STDIO_CLOSE in FC'. unfold F_STDIO_CLOSE, STDIO_CLOSE.
    zs. (* [comment removed for export] *)
    zs. zs. if_true. zs. zs. zs. zs.
    replace (ret_pc (Z_to_bv 64 0x1a8a8)) with (Z_to_bv 64 0x1a8a8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv delta [mkR]. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma fclose_S3a : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem)
      (flags mode : word) (readfn writefn buf bufsize prev next fd lbf : Z) (tail : list byte),
    rw_cells ssegs mm Fp (fclose_cells flags F_STDIO_CLOSE readfn writefn F_STDIO_SEEK buf bufsize prev next fd mode lbf tail) ->
    Z.land (bv_unsigned flags) F_PERM = 0 ->
    rw_cells ssegs mm NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    stk ssegs mm lo (bv_unsigned sp + -48) -> mem_inv ssegs mm ->
    evt ssegs (fun ms' => exists (x1' a1' a2' a3' : word) (m' : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                     (Z_to_bv 64 A_OFL_HEAD) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1abc0) fc None m' (seg_rom ssegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp - 48)] mm m' /\ wmono ssegs mm m' /\ mem_inv ssegs m'
        /\ stk ssegs m' lo (bv_unsigned sp + -48))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1ab9c) fc None mm (seg_rom ssegs)).
  Proof using FPLO GLO LO. pin_using (fun (FPLO GLO LO : unit) => tt).
    intros until tail. intros FC PERM NL ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bv_unsigned_in_range 64 flags) as FLR. unfold bv_modulus in FLR. cbn in FLR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp - 48)] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    pose proof FC as FC'. unfold fclose_cells, F_STDIO_CLOSE in FC'. unfold A_OFL_HEAD.
    zs. (* [comment removed for export] *)
    zs. zs.
    zs. if_cases KP; zify_cond KP.
    { exfalso. apply KP. rewrite Z_to_bv_unsigned, bv_wrap8_mod. unfold F_PERM in PERM.
      rewrite <- (Z.land_ones (bv_unsigned flags) 8) by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 8) 1) with 1. exact PERM. }
    zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0x1abb4)) with (Z_to_bv 64 0x1abb4 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. if_false. zs. (* [comment removed for export] *)
    carve_frame 16%nat ST. unfold NEED_LOCKS in NL. clear FC.
    zs. zs. zs. zs. zs. zs.
    zs. call_sp lock_spec; [exact NL | mi |].
    zs. zs. zs. zs. release_frame FR ST (bv_unsigned sp + -48). zs.
    zs. (* [comment removed for export] *)
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.

  (* [comment removed for export] *)
  Definition fcW (pv nx : Z) : list (Z * Z) :=
    [(bv_unsigned sp - 64, bv_unsigned sp - 48); (pv + 112, pv + (if pv =? 0 then 112 else 120));
     (nx + 104, nx + (if nx =? 0 then 104 else 112)); (A_OFL_HEAD, A_OFL_HEAD + 8)].

  Section Unlink.
    Variables (flags mode : word) (readfn writefn buf bufsize pv nx fd lbf : Z) (tail : list byte) (m0 : mem).
    Hypothesis PV0 : 0 <= pv.
    Hypothesis PVHI : pv + 1264 < 2^63.
    Hypothesis NX0 : 0 <= nx.
    Hypothesis NXHI : nx + 1264 < 2^63.
    Hypothesis PVF : pv <> 0 -> (pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x55000 <= pv) /\ 0 < pv.
    Hypothesis NXF : nx <> 0 -> (nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x55000 <= nx) /\ 0 < nx.
    Hypothesis PN : pv <> 0 -> nx <> 0 -> pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx.
    #[local] Definition FCc (mm : mem) : Prop :=
      rw_cells ssegs mm Fp (fclose_cells flags F_STDIO_CLOSE readfn writefn F_STDIO_SEEK buf bufsize pv nx fd mode lbf tail).

    (* [comment removed for export] *)
    Lemma fclose_S3b : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (pvn nxp : word) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells ssegs mm (pv + 112) [C8 pvn]) -> (nx <> 0 -> rw_cells ssegs mm (nx + 104) [C8 nxp]) ->
      rw_cells ssegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> stk ssegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono ssegs m0 mm -> mem_inv ssegs mm ->
      evt ssegs (fun ms' => exists m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 nx) (Z_to_bv 64 pv) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1abd0) fc None m' (seg_rom ssegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells ssegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells ssegs m' (nx + 104) [C8 nxp])
          /\ rw_cells ssegs m' A_OFL_HEAD [C8 (Z_to_bv 64 hd)] /\ stk ssegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono ssegs m0 m' /\ mem_inv ssegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 A_OFL_HEAD) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1abc0) fc None mm (seg_rom ssegs)).
    Proof using FPST NXF PN PV0 PVF PVHI. pin_using (fun (FPST NXF PN PV0 PVF PVHI : unit) => tt).
      intros until hd. intros FC PVC NXC OH ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (NXF' : nx = 0 \/ ((nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x55000 <= nx) /\ 0 < nx))
        by (destruct (Z.eq_dec nx 0) as [E|NE]; [left; exact E| right; exact (NXF NE)]).
      zs. zs. (* [comment removed for export] *)
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evt_done. exists mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [intros NZ; exfalso; apply NZ; exact K|]. split; [exact NXC|]. split; [exact OH|]. split; [exact ST|].
        split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        destruct (PVF K) as (P1 & P2 & P3 & P4). specialize (PVC K).
        replace (pv =? 0) with false in MU by (symmetry; apply Z.eqb_neq; exact K). cbv iota in MU.
        destruct NXF' as [NZ | (N1 & N2 & N3 & N4)]; [clear NXC| specialize (NXC ltac:(lia)); pose proof (PN K ltac:(lia)) as PN'].
        all: zs.
        all: apply evt_done; eexists; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|]; split; [intros _; exact PVC|].
        all: split; [first [intros _; exact NXC | intros NZ'; exfalso; exact (NZ' NZ)]|].
        all: split; [exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; replace (pv =? 0) with false by (symmetry; apply Z.eqb_neq; exact K); cbv iota; exact MU|].
        all: split; [exact WM| mi].
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3c : forall (x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (nxp : word) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells ssegs mm (pv + 112) [C8 (Z_to_bv 64 nx)]) -> (nx <> 0 -> rw_cells ssegs mm (nx + 104) [C8 nxp]) ->
      rw_cells ssegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> stk ssegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono ssegs m0 mm -> mem_inv ssegs mm ->
      evt ssegs (fun ms' => exists (a1' : word) m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 nx) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1abdc) fc None m' (seg_rom ssegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells ssegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells ssegs m' (nx + 104) [C8 (Z_to_bv 64 pv)])
          /\ rw_cells ssegs m' A_OFL_HEAD [C8 (Z_to_bv 64 hd)] /\ stk ssegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono ssegs m0 m' /\ mem_inv ssegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 nx) (Z_to_bv 64 pv) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1abd0) fc None mm (seg_rom ssegs)).
    Proof using FPST NX0 NXF NXHI PN PVF. pin_using (fun (FPST NX0 NXF NXHI PN PVF : unit) => tt).
      intros until hd. intros FC PVC NXC OH ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (PVF' : pv = 0 \/ ((pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x55000 <= pv) /\ 0 < pv))
        by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PVF NE)]).
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evt_done. eexists _, mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [exact PVC|]. split; [intros NZ; exfalso; apply NZ; exact K|]. split; [exact OH|]. split; [exact ST|].
        split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        destruct (NXF K) as (N1 & N2 & N3 & N4). specialize (NXC K).
        assert (PN' : pv = 0 \/ (pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx)) by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PN NE K)]).
        replace (nx =? 0) with false in MU by (symmetry; apply Z.eqb_neq; exact K). cbv iota in MU.
        destruct PVF' as [PZ | (P1 & P2 & P3 & P4)]; [clear PVC| destruct PN' as [PZ | PN']; [lia|]; specialize (PVC ltac:(lia))].
        all: zs; zs.
        all: apply evt_done; eexists _, _; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|].
        all: split; [first [intros _; exact PVC | intros NZ'; exfalso; exact (NZ' PZ)]|].
        all: split; [intros _; exact NXC|]; split; [exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; replace (nx =? 0) with false by (symmetry; apply Z.eqb_neq; exact K); cbv iota; exact MU|].
        all: split; [exact WM| mi].
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3d : forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells ssegs mm (pv + 112) [C8 (Z_to_bv 64 nx)]) -> (nx <> 0 -> rw_cells ssegs mm (nx + 104) [C8 (Z_to_bv 64 pv)]) ->
      rw_cells ssegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> 0 <= hd < 2^64 -> stk ssegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono ssegs m0 mm -> mem_inv ssegs mm ->
      evt ssegs (fun ms' => exists (a0' : word) m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1abec) fc None m' (seg_rom ssegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells ssegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells ssegs m' (nx + 104) [C8 (Z_to_bv 64 pv)])
          /\ rw_cells ssegs m' A_OFL_HEAD [C8 (Z_to_bv 64 (if hd =? Fp then nx else hd))] /\ stk ssegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono ssegs m0 m' /\ mem_inv ssegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 nx) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1abdc) fc None mm (seg_rom ssegs)).
    Proof using FPLO FPST Fp0 LO NXF NXHI PN PVF PVHI. pin_using (fun (FPLO FPST Fp0 LO NXF NXHI PN PVF PVHI : unit) => tt).
      intros until hd. intros FC PVC NXC OH HDR ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (PVF' : pv = 0 \/ ((pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x55000 <= pv) /\ 0 < pv))
        by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PVF NE)]).
      assert (NXF' : nx = 0 \/ ((nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x55000 <= nx) /\ 0 < nx))
        by (destruct (Z.eq_dec nx 0) as [E|NE]; [left; exact E| right; exact (NXF NE)]).
      zs. (* [comment removed for export] *)
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evt_done. eexists _, mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [exact PVC|]. split; [exact NXC|].
        split. { replace (hd =? Fp) with false by (symmetry; apply Z.eqb_neq; intros E; apply K; rewrite E; reflexivity). exact OH. }
        split; [exact ST|]. split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        assert (E : hd = Fp) by (rewrite ?Z.mod_small in K by lia; lia).
        (* [comment removed for export] *)
        destruct PVF' as [PZ | (P1 & P2 & P3 & P4)]; [clear PVC| specialize (PVC ltac:(lia))].
        all: destruct NXF' as [NZ | (N1 & N2 & N3 & N4)]; [clear NXC| specialize (NXC ltac:(lia))].
        all: zs; zs.
        all: apply evt_done; eexists _, _; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|].
        all: split; [first [exact PVC | intros _; exact PVC | intros NZ'; exfalso; exact (NZ' PZ)]|].
        all: split; [first [exact NXC | intros _; exact NXC | intros NZ'; exfalso; exact (NZ' NZ)]|].
        all: split; [rewrite E, Z.eqb_refl; exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; exact MU|]; split; [exact WM| mi].
    Qed.

    (* [comment removed for export] *)
    Lemma fclose_S3e : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
      FCc mm -> rw_cells ssegs mm A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> mem_inv ssegs mm ->
      evt ssegs (fun ms' => exists (a1' a2' a3' a4' a5' : word),
          ms' = MS (mkR (Z_to_bv 64 FCLOSE_FREE_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 Fp) a1' a2' a3' a4' a5' a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FREE_ENTRY') fc None mm (seg_rom ssegs))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1abec) fc None mm (seg_rom ssegs)).
    Proof using FPLO GLO LO. pin_using (fun (FPLO GLO LO : unit) => tt).
      intros until mm. intros FC OL MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold A_OFL_LOCK in OL. unfold A_OFL_HEAD, FCLOSE_FREE_RA, FREE_ENTRY'.
      zs. (* [comment removed for export] *)
      zs. zs. zs. (* [comment removed for export] *)
      call_sp unlock_spec0; [rewrite unsigned_lit by lia; exact OL | mi |].
      zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *)
      eapply evt_cut; [apply free_null|]. cbv beta. intros ms' ->.
      replace (ret_pc (Z_to_bv 64 0x1abf8)) with (Z_to_bv 64 0x1abf8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zs. zs. (* [comment removed for export] *)
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). cbv delta [mkR]. reflexivity.
    Qed.
  End Unlink.

  (* [comment removed for export] *)
  Lemma fclose_S4 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (jk : list byte),
    rw_cells ssegs mm (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk ssegs mm lo (bv_unsigned sp + -48) -> mem_inv ssegs mm ->
    evt ssegs (fun ms' =>
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None mm (seg_rom ssegs)
        /\ stk ssegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FCLOSE_FREE_RA) fc None mm (seg_rom ssegs)).
  Proof using LO. pin_using (fun (LO : unit) => tt).
    intros until jk. intros FR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    unfold FCLOSE_FREE_RA, A_OFL_HEAD.
    zs. (* [comment removed for export] *)
    do 5 zs. release_frame FR ST (bv_unsigned sp). zs. zs.
    apply evt_done. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
End Fclose.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan SecDiet.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Arr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Bytes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.InitMem.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_lock.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.Exit__S3.F_stdio_cs.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_fflush.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Definition FCLOSE : Z := 0x1b314.
Definition FCLOSE_FREE_RA : Z := 0x1b3c0.    (* [comment removed for export] *)
Definition FREE_ENTRY' : Z := 0x18f4c.
Local Ltac mi := match goal with H : mem_inv usegs _ |- _ => exact H end.

(* [comment removed for export] *)
Lemma free_null : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  evt usegs (fun ms' => ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (ret_pc ra) fc None m (seg_rom usegs))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FREE_ENTRY') fc None m (seg_rom usegs)).
Proof. intros. unfold FREE_ENTRY'. step. step. if_true. step. apply evt_done. reflexivity. Qed.

(* [comment removed for export] *)
Definition fclose_cells (flags : word) (closefn readfn writefn seekfn buf bufsize prev next fd : Z) (mode : word) (lbf : Z) (tail : list byte) : list cell :=
  [C1 (Z_to_bv 8 (bv_unsigned flags)); CB 3 (List.tl (le4 flags)); C4 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 closefn);
   C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C8 (Z_to_bv 64 readfn); C8 (Z_to_bv 64 writefn); C8 (Z_to_bv 64 seekfn);
   C8 (Z_to_bv 64 buf); C8 (Z_to_bv 64 bufsize);
   C8 (Z_to_bv 64 prev); C8 (Z_to_bv 64 next);
   C4 (Z_to_bv 64 fd); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0);
   C4 mode; C4 (Z_to_bv 64 0xffffffff); C4 (Z_to_bv 64 lbf); C4 (Z_to_bv 64 0);
   CB 16 (firstn 16 tail); C8 (Z_to_bv 64 0); CB 56 (skipn 24 tail)].

Lemma le8_zero : le8 (Z_to_bv 64 0) = repeat (Z_to_bv 8 0) 8.
Proof. reflexivity. Qed.

Lemma tail_split : forall (tail : list byte),
  firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
  firstn 16 tail ++ (repeat (Z_to_bv 8 0) 8 ++ skipn 24 tail) = tail.
Proof.
  intros tail GL. rewrite <- GL.
  replace (skipn 24 tail) with (skipn 8 (skipn 16 tail)) by (rewrite skipn_skipn; reflexivity).
  rewrite (firstn_skipn 8 (skipn 16 tail)). apply firstn_skipn.
Qed.

Lemma file_cells_tail_length : forall m Fp flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  rw_cells usegs m Fp (file_cells flags rpos rend closefn wend wpos wbase readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  length tail = 80%nat.
Proof.
  intros until tail. intros [[WF _] _]. unfold file_cells in WF. cbn [cells_wf cell_wf] in WF.
  repeat match type of WF with _ /\ _ => let X := fresh "X" in destruct WF as [X WF] end.
  assumption.
Qed.

Definition fclose_cells_recast__stmt : Prop := forall m Fp flags closefn readfn writefn seekfn buf bufsize prev next fd mode lbf tail,
  rw_cells usegs m Fp (file_cells flags 0 0 closefn 0 0 0 readfn writefn seekfn buf bufsize prev next fd mode lbf tail) ->
  firstn 8 (skipn 16 tail) = repeat (Z_to_bv 8 0) 8 ->
  rw_cells usegs m Fp (fclose_cells flags closefn readfn writefn seekfn buf bufsize prev next fd mode lbf tail).
Section Sz5.
Variables m Fp flags closefn readfn writefn seekfn buf bufsize prev next fd mode lbf tail : ltac2:(SecDiet.SzSec.tyM 'fclose_cells_recast__stmt "vvvvvvvvvvvvvvv" @m).
#[using="Type"] Lemma fclose_cells_recast__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_cells_recast__stmt "vvvvvvvvvvvvvvv").
Proof.
 intros FC GL.
  pose proof (file_cells_tail_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ FC) as TL.
  eapply rw_cells_recast; [exact FC| | |].
  - unfold fclose_cells. cbn -[skipn firstn]. rewrite length_firstn, length_skipn. repeat split; try reflexivity; lia.
  - unfold fclose_cells, file_cells. cbn -[skipn firstn le8 Z.shiftr repeat].
    rewrite le8_zero. rewrite !app_nil_r. rewrite (tail_split tail GL). reflexivity.
  - reflexivity.
Qed.
End Sz5.
Lemma fclose_cells_recast : ltac:(let t := eval cbv delta [fclose_cells_recast__stmt] in fclose_cells_recast__stmt in exact t).
Proof. intros m Fp flags closefn readfn writefn seekfn buf bufsize prev next fd mode lbf tail. ltac2:(SecDiet.SzSec.closeP 'fclose_cells_recast__body "vvvvvvvvvvvvvvv"). Qed.

Section Fclose.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (Fp lo : Z).
  Hypothesis LO : lo <= bv_unsigned sp - 512.
  Hypothesis GLO : 0x56000 <= lo.
  Hypothesis Fp0 : 0 < Fp.
  Hypothesis FPLO : Fp + 1264 <= lo.
  Hypothesis FPST : Fp + 1264 <= 0x10000 \/ 0x56000 <= Fp.

  (* [comment removed for export] *)
  Definition fclose_S1__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m : mem),
    stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (jk : list byte) (m1 : mem),
        ms' = MS (mkR (Z_to_bv 64 0x1b334) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 FFLUSH) fc None m1 (seg_rom usegs)
        /\ rw_cells usegs m1 (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
        /\ munch [(lo, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
        /\ stk usegs m1 lo (bv_unsigned sp + -48))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 Fp) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FCLOSE) fc None m (seg_rom usegs)).
  Section Sz6.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m : ltac2:(SecDiet.SzSec.tyM 'fclose_S1__stmt "vvvvvvvvvvvvvvv" @t0).
  Lemma fclose_S1__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_S1__stmt "vvvvvvvvvvvvvvv").
  Proof using LO. pin_using (fun (LO : unit) => tt).
 intros ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold FCLOSE, FFLUSH.
    carve_frame 48%nat ST.
    do 6 zs. zs. zs.
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz6.
  Lemma fclose_S1 : ltac:(let t := eval cbv delta [fclose_S1__stmt] in fclose_S1__stmt in exact t).
  Proof using LO. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m. ltac2:(SecDiet.SzSec.closeP 'fclose_S1__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fclose_S2__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (mm : mem)
      (flags mode : word) (readfn writefn buf bufsize prev next fd lbf : Z) (tail : list byte),
    rw_cells usegs mm Fp (fcells flags 0 0 F_STDIO_CLOSE 0 0 0 readfn writefn F_STDIO_SEEK buf bufsize prev next fd mode lbf tail) ->
    mem_inv usegs mm ->
    evt usegs (fun ms' => ms' = MS (mkR (Z_to_bv 64 0x1b35c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) a0
                                         (Z_to_bv 64 Fp) (Z_to_bv 64 F_STDIO_CLOSE) a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                    F (Z_to_bv 64 STDIO_CLOSE) fc None mm (seg_rom usegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 x19 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b334) fc None mm (seg_rom usegs)).
  Section Sz7.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 mm flags mode readfn writefn buf bufsize prev next fd lbf tail : ltac2:(SecDiet.SzSec.tyM 'fclose_S2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fclose_S2__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_S2__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using Type. pin_using tt.
 intros FC MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    pose proof FC as FC'. unfold fcells, file_cells, F_STDIO_CLOSE in FC'. unfold F_STDIO_CLOSE, STDIO_CLOSE.
    zs. (* [comment removed for export] *)
    zs. zs. if_true. zs. zs. zs. zs.
    replace (ret_pc (Z_to_bv 64 0x1b068)) with (Z_to_bv 64 0x1b068 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply evt_done. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz7.
  Lemma fclose_S2 : ltac:(let t := eval cbv delta [fclose_S2__stmt] in fclose_S2__stmt in exact t).
  Proof using Type. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 mm flags mode readfn writefn buf bufsize prev next fd lbf tail. ltac2:(SecDiet.SzSec.closeP 'fclose_S2__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fclose_S3a__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem)
      (flags mode : word) (readfn writefn buf bufsize prev next fd lbf : Z) (tail : list byte),
    rw_cells usegs mm Fp (fclose_cells flags F_STDIO_CLOSE readfn writefn F_STDIO_SEEK buf bufsize prev next fd mode lbf tail) ->
    Z.land (bv_unsigned flags) F_PERM = 0 ->
    rw_cells usegs mm NEED_LOCKS [C1 (Z_to_bv 8 0)] ->
    stk usegs mm lo (bv_unsigned sp + -48) -> mem_inv usegs mm ->
    evt usegs (fun ms' => exists (x1' a1' a2' a3' : word) (m' : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                     (Z_to_bv 64 A_OFL_HEAD) a1' a2' a3' a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x1b380) fc None m' (seg_rom usegs)
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp - 48)] mm m' /\ wmono usegs mm m' /\ mem_inv usegs m'
        /\ stk usegs m' lo (bv_unsigned sp + -48))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
               (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 (Z_to_bv 64 0) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1b35c) fc None mm (seg_rom usegs)).
  Section Sz8.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm flags mode readfn writefn buf bufsize prev next fd lbf tail : ltac2:(SecDiet.SzSec.tyM 'fclose_S3a__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma fclose_S3a__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_S3a__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvv").
  Proof using FPLO GLO LO. pin_using (fun (FPLO GLO LO : unit) => tt).
 intros FC PERM NL ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (bv_unsigned_in_range 64 flags) as FLR. unfold bv_modulus in FLR. cbn in FLR.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp - 48)] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    pose proof FC as FC'. unfold fclose_cells, F_STDIO_CLOSE in FC'. unfold A_OFL_HEAD.
    zs. (* [comment removed for export] *)
    zs. zs.
    zs. if_cases KP; zify_cond KP.
    { exfalso. apply KP. rewrite Z_to_bv_unsigned, bv_wrap8_mod. unfold F_PERM in PERM.
      rewrite <- (Z.land_ones (bv_unsigned flags) 8) by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 8) 1) with 1. exact PERM. }
    zs. zs. (* [comment removed for export] *)
    zs. (* [comment removed for export] *)
    replace (ret_pc (Z_to_bv 64 0x1b374)) with (Z_to_bv 64 0x1b374 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    zs. if_false. zs. (* [comment removed for export] *)
    carve_frame 16%nat ST. unfold NEED_LOCKS in NL. clear FC.
    zs. zs. zs. zs. zs. zs.
    zs. call_sp lock_spec; [exact NL | mi |].
    zs. zs. zs. zs. release_frame FR ST (bv_unsigned sp + -48). zs.
    zs. (* [comment removed for export] *)
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz8.
  Lemma fclose_S3a : ltac:(let t := eval cbv delta [fclose_S3a__stmt] in fclose_S3a__stmt in exact t).
  Proof using FPLO GLO LO. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm flags mode readfn writefn buf bufsize prev next fd lbf tail. ltac2:(SecDiet.SzSec.closeP 'fclose_S3a__body "vvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition fcW (pv nx : Z) : list (Z * Z) :=
    [(bv_unsigned sp - 64, bv_unsigned sp - 48); (pv + 112, pv + (if pv =? 0 then 112 else 120));
     (nx + 104, nx + (if nx =? 0 then 104 else 112)); (A_OFL_HEAD, A_OFL_HEAD + 8)].

  Section Unlink.
    Variables (flags mode : word) (readfn writefn buf bufsize pv nx fd lbf : Z) (tail : list byte) (m0 : mem).
    Hypothesis PV0 : 0 <= pv.
    Hypothesis PVHI : pv + 1264 < 2^63.
    Hypothesis NX0 : 0 <= nx.
    Hypothesis NXHI : nx + 1264 < 2^63.
    Hypothesis PVF : pv <> 0 -> (pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x56000 <= pv) /\ 0 < pv.
    Hypothesis NXF : nx <> 0 -> (nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x56000 <= nx) /\ 0 < nx.
    Hypothesis PN : pv <> 0 -> nx <> 0 -> pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx.
    #[local] Definition FCc (mm : mem) : Prop :=
      rw_cells usegs mm Fp (fclose_cells flags F_STDIO_CLOSE readfn writefn F_STDIO_SEEK buf bufsize pv nx fd mode lbf tail).

    (* [comment removed for export] *)
    Definition fclose_S3b__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (pvn nxp : word) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells usegs mm (pv + 112) [C8 pvn]) -> (nx <> 0 -> rw_cells usegs mm (nx + 104) [C8 nxp]) ->
      rw_cells usegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> stk usegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono usegs m0 mm -> mem_inv usegs mm ->
      evt usegs (fun ms' => exists m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 nx) (Z_to_bv 64 pv) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1b390) fc None m' (seg_rom usegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells usegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells usegs m' (nx + 104) [C8 nxp])
          /\ rw_cells usegs m' A_OFL_HEAD [C8 (Z_to_bv 64 hd)] /\ stk usegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 A_OFL_HEAD) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1b380) fc None mm (seg_rom usegs)).
    Section Sz9.
    Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm pvn nxp hd : ltac2:(SecDiet.SzSec.tyM 'fclose_S3b__stmt "vvvvvvvvvvvvvvvvvvv" @x1).
    Lemma fclose_S3b__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_S3b__stmt "vvvvvvvvvvvvvvvvvvv").
    Proof using FPST NXF PN PV0 PVF PVHI. pin_using (fun (FPST NXF PN PV0 PVF PVHI : unit) => tt).
 intros FC PVC NXC OH ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (NXF' : nx = 0 \/ ((nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x56000 <= nx) /\ 0 < nx))
        by (destruct (Z.eq_dec nx 0) as [E|NE]; [left; exact E| right; exact (NXF NE)]).
      zs. zs. (* [comment removed for export] *)
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evt_done. exists mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [intros NZ; exfalso; apply NZ; exact K|]. split; [exact NXC|]. split; [exact OH|]. split; [exact ST|].
        split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        destruct (PVF K) as (P1 & P2 & P3 & P4). specialize (PVC K).
        replace (pv =? 0) with false in MU by (symmetry; apply Z.eqb_neq; exact K). cbv iota in MU.
        destruct NXF' as [NZ | (N1 & N2 & N3 & N4)]; [clear NXC| specialize (NXC ltac:(lia)); pose proof (PN K ltac:(lia)) as PN'].
        all: zs.
        all: apply evt_done; eexists; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|]; split; [intros _; exact PVC|].
        all: split; [first [intros _; exact NXC | intros NZ'; exfalso; exact (NZ' NZ)]|].
        all: split; [exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; replace (pv =? 0) with false by (symmetry; apply Z.eqb_neq; exact K); cbv iota; exact MU|].
        all: split; [exact WM| mi].
    Qed.
    End Sz9.
    Lemma fclose_S3b : ltac:(let t := eval cbv delta [fclose_S3b__stmt] in fclose_S3b__stmt in exact t).
    Proof using FPST NXF PN PV0 PVF PVHI. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm pvn nxp hd. ltac2:(SecDiet.SzSec.closeP 'fclose_S3b__body "vvvvvvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition fclose_S3c__stmt : Prop := forall (x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (nxp : word) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells usegs mm (pv + 112) [C8 (Z_to_bv 64 nx)]) -> (nx <> 0 -> rw_cells usegs mm (nx + 104) [C8 nxp]) ->
      rw_cells usegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> stk usegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono usegs m0 mm -> mem_inv usegs mm ->
      evt usegs (fun ms' => exists (a1' : word) m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 nx) a1' a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1b39c) fc None m' (seg_rom usegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells usegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells usegs m' (nx + 104) [C8 (Z_to_bv 64 pv)])
          /\ rw_cells usegs m' A_OFL_HEAD [C8 (Z_to_bv 64 hd)] /\ stk usegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 nx) (Z_to_bv 64 pv) a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1b390) fc None mm (seg_rom usegs)).
    Section Sz10.
    Variables x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm nxp hd : ltac2:(SecDiet.SzSec.tyM 'fclose_S3c__stmt "vvvvvvvvvvvvvvvvv" @x1).
    Lemma fclose_S3c__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_S3c__stmt "vvvvvvvvvvvvvvvvv").
    Proof using FPST NX0 NXF NXHI PN PVF. pin_using (fun (FPST NX0 NXF NXHI PN PVF : unit) => tt).
 intros FC PVC NXC OH ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (PVF' : pv = 0 \/ ((pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x56000 <= pv) /\ 0 < pv))
        by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PVF NE)]).
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evt_done. eexists _, mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [exact PVC|]. split; [intros NZ; exfalso; apply NZ; exact K|]. split; [exact OH|]. split; [exact ST|].
        split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        destruct (NXF K) as (N1 & N2 & N3 & N4). specialize (NXC K).
        assert (PN' : pv = 0 \/ (pv + 1264 <= nx \/ nx + 1264 <= pv \/ pv = nx)) by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PN NE K)]).
        replace (nx =? 0) with false in MU by (symmetry; apply Z.eqb_neq; exact K). cbv iota in MU.
        destruct PVF' as [PZ | (P1 & P2 & P3 & P4)]; [clear PVC| destruct PN' as [PZ | PN']; [lia|]; specialize (PVC ltac:(lia))].
        all: zs; zs.
        all: apply evt_done; eexists _, _; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|].
        all: split; [first [intros _; exact PVC | intros NZ'; exfalso; exact (NZ' PZ)]|].
        all: split; [intros _; exact NXC|]; split; [exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; replace (nx =? 0) with false by (symmetry; apply Z.eqb_neq; exact K); cbv iota; exact MU|].
        all: split; [exact WM| mi].
    Qed.
    End Sz10.
    Lemma fclose_S3c : ltac:(let t := eval cbv delta [fclose_S3c__stmt] in fclose_S3c__stmt in exact t).
    Proof using FPST NX0 NXF NXHI PN PVF. intros x1 t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm nxp hd. ltac2:(SecDiet.SzSec.closeP 'fclose_S3c__body "vvvvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition fclose_S3d__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (hd : Z),
      FCc mm -> (pv <> 0 -> rw_cells usegs mm (pv + 112) [C8 (Z_to_bv 64 nx)]) -> (nx <> 0 -> rw_cells usegs mm (nx + 104) [C8 (Z_to_bv 64 pv)]) ->
      rw_cells usegs mm A_OFL_HEAD [C8 (Z_to_bv 64 hd)] -> 0 <= hd < 2^64 -> stk usegs mm lo (bv_unsigned sp + -48) ->
      munch (fcW pv nx) m0 mm -> wmono usegs m0 mm -> mem_inv usegs mm ->
      evt usegs (fun ms' => exists (a0' : word) m',
          ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       a0' a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 0x1b3ac) fc None m' (seg_rom usegs)
          /\ FCc m' /\ (pv <> 0 -> rw_cells usegs m' (pv + 112) [C8 (Z_to_bv 64 nx)]) /\ (nx <> 0 -> rw_cells usegs m' (nx + 104) [C8 (Z_to_bv 64 pv)])
          /\ rw_cells usegs m' A_OFL_HEAD [C8 (Z_to_bv 64 (if hd =? Fp then nx else hd))] /\ stk usegs m' lo (bv_unsigned sp + -48)
          /\ munch (fcW pv nx) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m')
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 (Z_to_bv 64 nx) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1b39c) fc None mm (seg_rom usegs)).
    Section Sz11.
    Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm hd : ltac2:(SecDiet.SzSec.tyM 'fclose_S3d__stmt "vvvvvvvvvvvvvvvvv" @x1).
    Lemma fclose_S3d__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_S3d__stmt "vvvvvvvvvvvvvvvvv").
    Proof using FPLO FPST Fp0 LO NXF NXHI PN PVF PVHI. pin_using (fun (FPLO FPST Fp0 LO NXF NXHI PN PVF PVHI : unit) => tt).
 intros FC PVC NXC OH HDR ST MU WM MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold fcW, A_OFL_HEAD in MU. unfold A_OFL_HEAD in OH |- *.
      assert (PVF' : pv = 0 \/ ((pv + 1264 <= Fp \/ Fp + 1264 <= pv) /\ pv + 1264 <= lo /\ (pv + 1264 <= 0x10000 \/ 0x56000 <= pv) /\ 0 < pv))
        by (destruct (Z.eq_dec pv 0) as [E|NE]; [left; exact E| right; exact (PVF NE)]).
      assert (NXF' : nx = 0 \/ ((nx + 1264 <= Fp \/ Fp + 1264 <= nx) /\ nx + 1264 <= lo /\ (nx + 1264 <= 0x10000 \/ 0x56000 <= nx) /\ 0 < nx))
        by (destruct (Z.eq_dec nx 0) as [E|NE]; [left; exact E| right; exact (NXF NE)]).
      zs. (* [comment removed for export] *)
      zs. if_cases K; zify_cond K.
      - (* [comment removed for export] *)
        apply evt_done. eexists _, mm. split; [cbv delta [mkR]; reflexivity|].
        split; [exact FC|]. split; [exact PVC|]. split; [exact NXC|].
        split. { replace (hd =? Fp) with false by (symmetry; apply Z.eqb_neq; intros E; apply K; rewrite E; reflexivity). exact OH. }
        split; [exact ST|]. split; [unfold fcW, A_OFL_HEAD; exact MU|]. split; [exact WM| mi].
      - (* [comment removed for export] *)
        assert (E : hd = Fp) by (rewrite ?Z.mod_small in K by lia; lia).
        (* [comment removed for export] *)
        destruct PVF' as [PZ | (P1 & P2 & P3 & P4)]; [clear PVC| specialize (PVC ltac:(lia))].
        all: destruct NXF' as [NZ | (N1 & N2 & N3 & N4)]; [clear NXC| specialize (NXC ltac:(lia))].
        all: zs; zs.
        all: apply evt_done; eexists _, _; split; [cbv delta [mkR]; reflexivity|].
        all: split; [exact FC|].
        all: split; [first [exact PVC | intros _; exact PVC | intros NZ'; exfalso; exact (NZ' PZ)]|].
        all: split; [first [exact NXC | intros _; exact NXC | intros NZ'; exfalso; exact (NZ' NZ)]|].
        all: split; [rewrite E, Z.eqb_refl; exact OH|]; split; [exact ST|].
        all: split; [unfold fcW, A_OFL_HEAD; exact MU|]; split; [exact WM| mi].
    Qed.
    End Sz11.
    Lemma fclose_S3d : ltac:(let t := eval cbv delta [fclose_S3d__stmt] in fclose_S3d__stmt in exact t).
    Proof using FPLO FPST Fp0 LO NXF NXHI PN PVF PVHI. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm hd. ltac2:(SecDiet.SzSec.closeP 'fclose_S3d__body "vvvvvvvvvvvvvvvvv"). Qed.

    (* [comment removed for export] *)
    Definition fclose_S3e__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem),
      FCc mm -> rw_cells usegs mm A_OFL_LOCK [C4 (Z_to_bv 64 0)] -> mem_inv usegs mm ->
      evt usegs (fun ms' => exists (a1' a2' a3' a4' a5' : word),
          ms' = MS (mkR (Z_to_bv 64 FCLOSE_FREE_RA) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                       (Z_to_bv 64 Fp) a1' a2' a3' a4' a5' a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FREE_ENTRY') fc None mm (seg_rom usegs))
        (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
                 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x1b3ac) fc None mm (seg_rom usegs)).
    Section Sz12.
    Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm : ltac2:(SecDiet.SzSec.tyM 'fclose_S3e__stmt "vvvvvvvvvvvvvvvvv" @x1).
    Lemma fclose_S3e__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_S3e__stmt "vvvvvvvvvvvvvvvvv").
    Proof using FPLO GLO LO. pin_using (fun (FPLO GLO LO : unit) => tt).
 intros FC OL MI.
      pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
      pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
      unfold FCc, fclose_cells, F_STDIO_CLOSE, F_STDIO_SEEK in FC. unfold A_OFL_LOCK in OL. unfold A_OFL_HEAD, FCLOSE_FREE_RA, FREE_ENTRY'.
      zs. (* [comment removed for export] *)
      zs. zs. zs. (* [comment removed for export] *)
      call_sp unlock_spec0; [rewrite unsigned_lit by lia; exact OL | mi |].
      zs. (* [comment removed for export] *)
      zs. (* [comment removed for export] *)
      eapply evt_cut; [apply free_null|]. cbv beta. intros ms' ->.
      replace (ret_pc (Z_to_bv 64 0x1b3b8)) with (Z_to_bv 64 0x1b3b8 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      zs. zs. (* [comment removed for export] *)
      apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end). cbv delta [mkR]. reflexivity.
    Qed.
    End Sz12.
    Lemma fclose_S3e : ltac:(let t := eval cbv delta [fclose_S3e__stmt] in fclose_S3e__stmt in exact t).
    Proof using FPLO GLO LO. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm. ltac2:(SecDiet.SzSec.closeP 'fclose_S3e__body "vvvvvvvvvvvvvvvvv"). Qed.
  End Unlink.

  (* [comment removed for export] *)
  Definition fclose_S4__stmt : Prop := forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (jk : list byte),
    rw_cells usegs mm (bv_unsigned sp + -48) [CB 8 jk; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs mm lo (bv_unsigned sp + -48) -> mem_inv usegs mm ->
    evt usegs (fun ms' =>
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (ret_pc ra) fc None mm (seg_rom usegs)
        /\ stk usegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 Fp) (Z_to_bv 64 0)
               a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 0) (Z_to_bv 64 A_OFL_HEAD) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FCLOSE_FREE_RA) fc None mm (seg_rom usegs)).
  Section Sz13.
  Variables x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm jk : ltac2:(SecDiet.SzSec.tyM 'fclose_S4__stmt "vvvvvvvvvvvvvvvvvv" @x1).
  Lemma fclose_S4__body : ltac2:(SecDiet.SzSec.bodyP 'fclose_S4__stmt "vvvvvvvvvvvvvvvvvv").
  Proof using LO. pin_using (fun (LO : unit) => tt).
 intros FR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    unfold FCLOSE_FREE_RA, A_OFL_HEAD.
    zs. (* [comment removed for export] *)
    do 5 zs. release_frame FR ST (bv_unsigned sp). zs. zs.
    apply evt_done. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
  End Sz13.
  Lemma fclose_S4 : ltac:(let t := eval cbv delta [fclose_S4__stmt] in fclose_S4__stmt in exact t).
  Proof using LO. intros x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm jk. ltac2:(SecDiet.SzSec.closeP 'fclose_S4__body "vvvvvvvvvvvvvvvvvv"). Qed.
End Fclose.
End TwB.
End F_fclose.

(* [comment removed for export] *)
Module F_mkstemp.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import Tac ITree Nodes Decode SysStep ImgSrc3.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Prelim Monad Fmt StdioCore Stdio. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require Adapter__Spec. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec Require PcapPrelim PcapTypes PcapPure Pcap. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require FileCells__Musl. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl Require AmoStep__Musl. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_lock__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memchr__S3. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memcpy. From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3 Require F_memmove__S3. Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strlen OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strrchr OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_memmove OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import LiaPin.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require SecDiet.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require Import KeepHyps.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv ssegs _ |- _ => exact H end.

Definition open_w_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) ->
  bytes_at ssegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells ssegs m (errno_addr tp) [C4 errv] ->
  rw_cells ssegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells ssegs m ssp_guard [C8 canary] ->
  mem_inv ssegs m ->
  a1 = Z_to_bv 64 577 (* [comment removed for export] *) -> a2 = Z_to_bv 64 384 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  (Namei.path_has_slash path = false \/ path = Uapi.devnull_path) ->   (* [comment removed for export] *)
  (lo <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
  (got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl ssegs (at_node ssegs) (npeek ssegs) (enode (NOpenW path 384) dec_openw)
       (epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x18538) fc None m (seg_rom ssegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv canary lo : ltac2:(SecDiet.SzSec.tyM 'open_w_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma open_w_spec__body : ltac2:(SecDiet.SzSec.bodyP 'open_w_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros ST SRC ERR GOT SSP MI -> Ha2 NUL NSLASH LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl ssegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  apply impl_enode.
  carve_frame 96%nat ST.
  do 18 step.
  if_true. subst a2.
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: C8 (Z_to_bv 64 384) :: ?rest) =>
    assert (FR' : rw_cells ssegs mm A (c0 :: c1 :: c2 :: c3 :: c4 :: C4 (Z_to_bv 64 384) :: C4 (Z_to_bv 64 0) :: rest))
      by (pose proof (proj1 (proj1 FR)) as WF; cbn [cells_wf cell_wf] in WF; eapply (rw_cells_recast mm A _ _ FR); [cbn [cells_wf cell_wf]; (keep_hyps sp tp a0 path junk WF; tauto)| reflexivity| reflexivity]);
    clear FR; rename FR' into FR
  end.
  step.
  all: match goal with |- evt _ _ ?ms => idtac "OW2:" ms end.
  do 8 step. (* [comment removed for export] *) do 8 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | (keep_hyps sp a0 path lo LO; lia) | (keep_hyps sp tp a0 path SEP1; lia) | (keep_hyps tp a0 path TP; lia) | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - destruct Hdec as (-> & Hfd & Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. unfold eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | (keep_hyps sp a0 path lo LO; lia) | (keep_hyps sp tp a0 path SEP1; lia) | (keep_hyps tp a0 path TP; lia) | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed.
End Sz1.
Lemma open_w_spec : ltac:(let t := eval cbv delta [open_w_spec__stmt] in open_w_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv canary lo. ltac2:(SecDiet.SzSec.closeP 'open_w_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
#[local] Definition b8 (z : Z) : byte := Z_to_bv 8 z.
Definition TMPL : list byte := map b8 TEMPLATE.                                    (* [comment removed for export] *)
Definition SEALED : list byte := map b8 (str "/tmp/libpcap_fuzz_pcap.000000"%string).   (* [comment removed for export] *)
Definition TMPN : list byte := map b8 TMPNAME.                                     (* [comment removed for export] *)
Definition MKSTEMP : Z := 0x17b18.

Lemma TMPL_len : length TMPL = 29%nat. Proof. reflexivity. Qed.
Lemma SEALED_len : length SEALED = 29%nat. Proof. reflexivity. Qed.
Lemma TMPN_len : length TMPN = 24%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition TMPL0 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 0].      (* [comment removed for export] *)
Definition SEALED0 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 0].  (* [comment removed for export] *)
Definition TMP5 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47].   (* [comment removed for export] *)
Definition TMPN0 : list byte := [Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 0].  (* [comment removed for export] *)
Lemma TMPL0_eq : TMPL ++ [Z_to_bv 8 0] = TMPL0. Proof. vm_compute. reflexivity. Qed.
Lemma TMPL0_len_30 : length TMPL0 = 30%nat. Proof. reflexivity. Qed.
Lemma SEALED0_eq : SEALED ++ [Z_to_bv 8 0] = SEALED0. Proof. vm_compute. reflexivity. Qed.
Lemma TMPN0_eq : TMPN ++ [Z_to_bv 8 0] = TMPN0. Proof. vm_compute. reflexivity. Qed.



(* [comment removed for export] *)
Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(D, D + N)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ rw_cells ssegs m' D [CB (Z.to_nat N) src] /\ bytes_at ssegs m' S src.
Definition memcpy_callw__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D S N : Z) (src junk : list byte),
  bytes_at ssegs m S src -> length src = Z.to_nat N -> rw_cells ssegs m D [CB (Z.to_nat N) junk] ->
  (S + N <= D \/ D + N <= S) -> 0 <= N -> 0 <= D -> D + N < 2^64 -> 0 <= S -> S + N < 2^64 -> mem_inv ssegs m ->
  evt ssegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x207e0) fc None m (seg_rom ssegs)).
Section Sz10.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S N src junk : ltac2:(SecDiet.SzSec.tyM 'memcpy_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memcpy_callw__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
  intros SRC LEN DST SEP HN HD HDN HS HSN MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D : word) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S : word) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N : word) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec with (junk := junk); rewrite ?ED, ?ES, ?EN; [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' PO. unfold memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in PO. exact PO.
Qed.
End Sz10.
Lemma memcpy_callw : ltac:(let t := eval cbv delta [memcpy_callw__stmt] in memcpy_callw__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S N src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_callw__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition strrchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A c : Z) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strrchr_res A c str)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ stk ssegs m' lo (bv_unsigned sp) /\ bytes_at ssegs m' A (str ++ Z_to_bv 8 0 :: slack).
Lemma strrchr_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A c : Z) (str slack : list byte) (lo : Z),
  stk ssegs m lo (bv_unsigned sp) -> bytes_at ssegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> mem_inv ssegs m -> lo <= bv_unsigned sp - 32 ->
  (A + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A) ->
  0 <= A < 2^64 -> 0 <= c < 256 ->
  evt ssegs (strrchr_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x210e0) fc None m (seg_rom ssegs)).
Proof.
  intros until lo. intros ST STR NONUL PAD MI LO SEP HA HC.
  assert (EA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 c : word) = c) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply strrchr_spec; rewrite ?EA, ?EC; [exact ST | exact STR | exact NONUL | exact PAD | exact MI | exact LO | exact SEP]. }
  intros ms' PO. unfold strrchr_post, strrchr_postv in *. rewrite EA, EC, (Z.mod_small c 256) in PO by lia. exact PO.
Qed.

Definition strlen_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (str slack : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ bytes_at ssegs m' A (str ++ Z_to_bv 8 0 :: slack).
Lemma strlen_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A : Z) (str slack : list byte),
  bytes_at ssegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> mem_inv ssegs m -> 0 <= A < 2^64 ->
  evt ssegs (strlen_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2100c) fc None m (seg_rom ssegs)).
Proof.
  intros until slack. intros STR NONUL PAD MI HA.
  assert (EA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply strlen_spec; rewrite ?EA; [exact STR | exact NONUL | exact PAD | exact MI]. }
  intros ms' PO. unfold strlen_post, strlen_postv in *. rewrite EA in PO. exact PO.
Qed.

Definition memmove_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D k N : Z) (bs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ssegs)
    /\ munch [(D, D + N)] m m' /\ wmono ssegs m m' /\ mem_inv ssegs m'
    /\ u8arr ssegs m' D (firstn (Z.to_nat N) (skipn (Z.to_nat k) bs) ++ skipn (Z.to_nat N) bs).
Lemma memmove_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (bs : list byte) (D k N : Z),
  u8arr ssegs m D bs -> mem_inv ssegs m -> 1 <= k -> 0 <= N < 2^62 -> length bs = Z.to_nat (k + N) -> 0 <= D -> D + k < 2^64 ->
  evt ssegs (memmove_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D k N bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (D + k)) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20be4) fc None m (seg_rom ssegs)).
Proof.
  intros until N. intros ARR MI HK HN LEN HD HDK.
  assert (ED : bv_unsigned (Z_to_bv 64 D : word) = D) by (apply unsigned_lit; lia).
  assert (EDK : bv_unsigned (Z_to_bv 64 (D + k) : word) = D + k) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memmove_spec; rewrite ?ED, ?EDK; [exact ARR | exact MI | reflexivity | reflexivity | exact HK | exact HN | exact LEN]. }
  intros ms' PO. unfold memmove_post, memmove_postv in *. rewrite ED in PO. exact PO.
Qed.

Section Mk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (NAME lo : Z) (n : nat).
  Hypothesis LO : lo <= bv_unsigned sp - 144.
  Hypothesis GLO : 0x55000 <= lo.
  Hypothesis N0 : 0 < NAME.
  Hypothesis NSEP : NAME + Z.of_nat n <= lo \/ bv_unsigned sp <= NAME.
  Hypothesis NHI : NAME + Z.of_nat n <= 2^47.
  Hypothesis NR : (38 <= n <= 4096)%nat.
  Hypothesis NROM : NAME + Z.of_nat n <= 0x10000 \/ 0x55000 <= NAME.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mk_S1__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (m : mem),
    rw_cells ssegs m NAME [CB 30 TMPL0; CB (n - 30) rest] ->
    stk ssegs m lo (bv_unsigned sp) -> mem_inv ssegs m ->
    evt ssegs (fun ms' => exists (x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (jk : list byte) (m1 : mem),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 NAME) (Z_to_bv 64 0) (Z_to_bv 64 29) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x17b64) fc None m1 (seg_rom ssegs)
        /\ rw_cells ssegs m1 (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono ssegs m m1 /\ mem_inv ssegs m1
        /\ stk ssegs m1 lo (bv_unsigned sp + -32))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MKSTEMP) fc None m (seg_rom ssegs)).
  Section Sz14.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest m : ltac2:(SecDiet.SzSec.tyM 'mk_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma mk_S1__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using GLO LO N0 NHI NR NROM NSEP. pin_using (fun (GLO LO N0 NHI NR NROM NSEP : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros BUF ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl ssegs m) as WM.
    unfold MKSTEMP.
    carve_frame 32%nat ST.
    zs. zs. zs. zs. zs. zs.
    zs. if_cases K0; zify_cond K0. 1:{ exfalso. rewrite ?Z.mod_small in K0 by lia. lia. }
    zs. zs. if_cases K1; zify_cond K1. 1:{ exfalso. revert K1. cbn. lia. }
    zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (STR : bytes_at ssegs mm (bv_unsigned (Z_to_bv 64 NAME : word)) (TMPL ++ Z_to_bv 8 0 :: rest)) end.
    { rewrite unsigned_lit by lia.
      pose proof BUF as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r, <- TMPL0_eq, <- app_assoc in HB. exact HB. }
    zs. call_sp strlen_spec; [exact STR | unfold TMPL, TEMPLATE; cbn; clear; intuition discriminate | | mi | ].
    { rewrite unsigned_lit by lia. rewrite TMPL_len. pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LR & _).
      eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; lia|]. lia. }
    rewrite TMPL_len. zs. zs. if_cases K2; zify_cond K2. 2:{ exfalso. revert K2. rewrite ?unsigned_lit by lia. cbn. lia. }
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz14.
  Lemma mk_S1 : ltac:(let t := eval cbv delta [mk_S1__stmt] in mk_S1__stmt in exact t).
  Proof using GLO LO N0 NHI NR NROM NSEP. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest m. ltac2:(SecDiet.SzSec.closeP 'mk_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mk_S2__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (mm : mem),
    rw_cells ssegs mm NAME [CB 30 TMPL0; CB (n - 30) rest] -> mem_inv ssegs mm ->
    evt ssegs (fun ms' => exists (a4' : word),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0)
                     (Z_to_bv 64 (NAME + 23)) (Z_to_bv 64 0) (Z_to_bv 64 88) (Z_to_bv 64 (NAME + 29)) a4' a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x17b90) fc None mm (seg_rom ssegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0) (Z_to_bv 64 29) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17b64) fc None mm (seg_rom ssegs)).
  Section Sz15.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest mm : ltac2:(SecDiet.SzSec.tyM 'mk_S2__stmt "vvvvvvvvvvvvvvvvv" @x1).
  Lemma mk_S2__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S2__stmt "vvvvvvvvvvvvvvvvv").
  Proof using N0 NHI NR. pin_using (fun (N0 NHI NR : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros BUF MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    unfold TMPL0 in BUF.
    zs. zs. zs. replace (NAME + 29 - 0 + -6) with (NAME + 23) by lia. zs. zs. zs.
    (* [comment removed for export] *)
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_false.
    apply evt_done. eexists. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz15.
  Lemma mk_S2 : ltac:(let t := eval cbv delta [mk_S2__stmt] in mk_S2__stmt in exact t).
  Proof using N0 NHI NR. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest mm. ltac2:(SecDiet.SzSec.closeP 'mk_S2__body "vvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mk_S3__stmt : Prop := forall (x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (mm : mem) (jk : list byte),
    rw_cells ssegs mm NAME [CB 30 TMPL0; CB (n - 30) rest] ->
    rw_cells ssegs mm (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
    stk ssegs mm lo (bv_unsigned sp + -32) -> mem_inv ssegs mm ->
    evt ssegs (fun ms' => exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 NAME) (Z_to_bv 64 (NAME + 5))
                     a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x17bc8) fc None m' (seg_rom ssegs)
        /\ rw_cells ssegs m' NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]
        /\ rw_cells ssegs m' (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp - 32); (NAME, NAME + 30)] mm m' /\ wmono ssegs mm m' /\ mem_inv ssegs m'
        /\ stk ssegs m' lo (bv_unsigned sp + -32))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0)
               (Z_to_bv 64 (NAME + 23)) (Z_to_bv 64 0) (Z_to_bv 64 88) (Z_to_bv 64 (NAME + 29)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17b90) fc None mm (seg_rom ssegs)).
  Section Sz16.
  Variables x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 rest mm jk : ltac2:(SecDiet.SzSec.tyM 'mk_S3__stmt "vvvvvvvvvvvvvvv" @x1).
  Lemma mk_S3__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S3__stmt "vvvvvvvvvvvvvvv").
  Proof using GLO LO N0 NHI NR NROM NSEP. pin_using (fun (GLO LO N0 NHI NR NROM NSEP : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros BUF FR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp - 32); (NAME, NAME + 30)] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LR & _).
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB ssegs mm NAME [] 30 TMPL0 [CB (n - 30) rest] [23%nat; 6%nat; 1%nat] BUF eq_refl) as B4.
    cbn [app mk_CB_cells] in B4. unfold TMPL0 in B4. cbn [firstn skipn] in B4. clear BUF.
    apply (proj1 (rw_cells_app ssegs mm NAME [_] _)) in B4 as [P1 B4]. apply (proj1 (rw_cells_app ssegs mm _ [_] _)) in B4 as [DST B4].
    cbn [cells_size csize Nat.add] in DST, B4.
    replace (NAME + Z.of_nat 23) with (NAME + 23) in DST by lia. replace (NAME + Z.of_nat 23 + Z.of_nat 6) with (NAME + 29) in B4 by lia.
    zs. zs.
    zs. call_sp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fopen.memset_callw; [exact DST | (keep_hyps n rest; lia) | (keep_hyps NAME n rest N0; lia) | (keep_hyps NAME n rest NHI; lia) | (keep_hyps n rest; lia) | mi |].
    match goal with H : rw_cells ssegs _ (NAME + 23) [CB _ (repeat _ _)] |- _ => rename H into SEALC end.
    change (Z.to_nat 6) with 6%nat in SEALC.
    replace (repeat (Z_to_bv 8 (48 mod 256)) 6) with (map b8 SEAL) in SEALC by (vm_compute; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
    (* [comment removed for export] *)
    assert (STR2 : bytes_at ssegs m2 NAME (SEALED ++ Z_to_bv 8 0 :: rest)).
    { pose proof (proj2 (proj1 P1)) as X1. pose proof (proj2 (proj1 SEALC)) as X2. pose proof (proj2 (proj1 B4)) as X3.
      cbn [cells_bytes cbytes app] in X1, X2, X3. try rewrite app_nil_r in X1. try rewrite app_nil_r in X2.
      assert (E : SEALED ++ Z_to_bv 8 0 :: rest = (firstn 23 TMPL0 ++ map b8 SEAL) ++ (Z_to_bv 8 0 :: rest)).
      { cbv -[Z_to_bv]. reflexivity. }
      rewrite E. apply (proj2 (bytes_at_app _ _ _ _ _)). split.
      - apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact X1|].
        match goal with |- bytes_at _ _ ?a _ => replace a with (NAME + 23) by (cbn [length firstn app map TMPL0 Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Nat2Z.inj_succ; cbn; lia) end. exact X2.
      - match goal with |- bytes_at _ _ ?a _ => replace a with (NAME + 29) by (rewrite length_app, length_firstn, length_map; cbn; lia) end.
        rewrite app_nil_r in X3. exact X3. }
    (* [comment removed for export] *)
    zs. zs. zs.
    call_sp strrchr_callw; [exact ST | exact STR2 | unfold SEALED; cbn; clear; intuition discriminate | rewrite SEALED_len; eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; (keep_hyps n rest; lia)| (keep_hyps n rest NRZ LR; lia)]
                          | mi | (keep_hyps sp lo n rest LO; lia) | rewrite SEALED_len; (keep_hyps sp NAME lo n rest LO NSEP LR; lia) | (keep_hyps NAME n rest N0 NHI; lia) | (keep_hyps n rest; lia) | ].
    assert (LB : last_byte 47 (SEALED ++ [Z_to_bv 8 0]) = Some 4%nat) by (vm_compute; reflexivity).
    unfold strrchr_res, memrchr_res. rewrite LB. change (NAME + Z.of_nat 4) with (NAME + 4).
    zs. if_cases KZ; zify_cond KZ. 1:{ exfalso. rewrite ?Z.mod_small in KZ by lia. lia. }
    zs. zs.
    replace (NAME + 4 + 1) with (NAME + 5) by lia.
    (* [comment removed for export] *)
    match goal with H : bytes_at ssegs _ NAME (SEALED ++ _) |- _ => rename H into STR3 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m3 end.
    assert (STR5 : bytes_at ssegs m3 (NAME + 5) (TMPN ++ Z_to_bv 8 0 :: rest)).
    { assert (E5 : SEALED ++ Z_to_bv 8 0 :: rest = TMP5 ++ (TMPN ++ Z_to_bv 8 0 :: rest)) by (cbv -[Z_to_bv]; reflexivity).
      rewrite E5 in STR3. apply (proj1 (bytes_at_app _ _ _ _ _)) in STR3 as [_ STR3]. cbn [length TMP5 Z.of_nat Pos.of_succ_nat Pos.succ] in STR3.
      exact STR3. }
    zs. call_sp strlen_callw; [exact STR5 | unfold TMPN, TMPNAME; cbn; clear; intuition discriminate | rewrite TMPN_len; eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; (keep_hyps n rest; lia)| (keep_hyps n rest NRZ LR; lia)] | mi | (keep_hyps NAME n rest N0 NHI; lia) | ].
    rewrite TMPN_len.
    zs. zs. zs. replace (Z.of_nat 24 + 1) with 25 by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m4 end.
    match goal with H : rw_cells ssegs m4 NAME [CB 23 _] |- _ => rename H into Q1 end.
    match goal with H : rw_cells ssegs m4 (NAME + 23) _ |- _ => rename H into Q2 end.
    match goal with H : rw_cells ssegs m4 (NAME + 29) _ |- _ => rename H into Q3 end.
    apply (proj1 (rw_cells_app ssegs m4 (NAME + 29) [_] _)) in Q3 as [Q3 RESTC]. cbn [cells_size csize Nat.add] in RESTC.
    replace (NAME + 29 + Z.of_nat 1) with (NAME + 30) in RESTC by lia.
    assert (J1 : rw_cells ssegs m4 (NAME + 23) ([CB 6 (map b8 SEAL)] ++ [CB 1 [Z_to_bv 8 0]])).
    { apply (proj2 (rw_cells_app ssegs m4 (NAME + 23) _ _)). split; [exact Q2|]. cbn [cells_size csize Nat.add]. replace (NAME + 23 + Z.of_nat 6) with (NAME + 29) by lia. exact Q3. }
    assert (J2 : rw_cells ssegs m4 NAME ([CB 23 (firstn 23 TMPL0)] ++ ([CB 6 (map b8 SEAL)] ++ [CB 1 [Z_to_bv 8 0]]))).
    { apply (proj2 (rw_cells_app ssegs m4 NAME _ _)). split; [unfold TMPL0; cbn [firstn]; exact Q1|]. cbn [cells_size csize Nat.add]. replace (NAME + Z.of_nat 23) with (NAME + 23) by lia. exact J1. }
    assert (B30 : rw_cells ssegs m4 NAME [CB 30 SEALED0]).
    { eapply (rw_cells_recast m4 NAME _ _ J2); [cbn; split; [reflexivity| exact I] | cbv -[Z_to_bv]; reflexivity | reflexivity]. }
    clear Q1 Q2 Q3 J1 J2.
    pose proof (u8arr_of_rw_cells ssegs m4 NAME 30 SEALED0 B30) as ARR.
    zs. call_sp memmove_callw; [exact ARR | mi | (keep_hyps n rest; lia) | (keep_hyps n rest; lia) | reflexivity | (keep_hyps NAME n rest N0; lia) | (keep_hyps NAME n rest NHI; lia) | ].
    match goal with H : u8arr ssegs _ NAME _ |- _ => rename H into ARR2 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m5 end.
    pose proof (rw_cells_of_u8arr ssegs m5 NAME _ ARR2) as B30'.
    assert (B30n : rw_cells ssegs m5 NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0)]).
    { eapply (rw_cells_recast m5 NAME _ _ B30'); [cbn; split; [reflexivity| exact I] | cbv -[Z_to_bv]; reflexivity | reflexivity]. }
    match goal with H : rw_cells ssegs m5 (NAME + 30) _ |- _ => rename H into RESTC5 end.
    assert (BUF5 : rw_cells ssegs m5 NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]).
    { apply (proj2 (rw_cells_app ssegs m5 NAME [_] [_])). split; [exact B30n|]. cbn [cells_size csize Nat.add]. replace (NAME + Z.of_nat 30) with (NAME + 30) by lia. exact RESTC5. }
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact BUF5|].
    split; [match goal with H : rw_cells ssegs m5 (bv_unsigned sp + -32) _ |- _ => exact H end|].
    split; [exact MU|]. split; [exact WM|]. split; [mi|].
    match goal with H : stk ssegs m5 lo _ |- _ => exact H end.
  Qed.
  End Sz16.
  Lemma mk_S3 : ltac:(let t := eval cbv delta [mk_S3__stmt] in mk_S3__stmt in exact t).
  Proof using GLO LO N0 NHI NR NROM NSEP. intros x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 rest mm jk. ltac2:(SecDiet.SzSec.closeP 'mk_S3__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mk_S4__stmt : Prop := forall (x1 t0 t1 t2 sA sB a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (jk : list byte),
    rw_cells ssegs mm (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
    stk ssegs mm lo (bv_unsigned sp + -32) -> mem_inv ssegs mm ->
    evt ssegs (fun ms' =>
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) (Z_to_bv 64 577) (Z_to_bv 64 384) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x18538) fc None mm (seg_rom ssegs)
        /\ stk ssegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) sB a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x17bc8) fc None mm (seg_rom ssegs)).
  Section Sz17.
  Variables x1 t0 t1 t2 sA sB a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm jk : ltac2:(SecDiet.SzSec.tyM 'mk_S4__stmt "vvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma mk_S4__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S4__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using LO NR. pin_using (fun (LO NR : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
    intros FR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl ssegs mm) as WM.
    zs. zs. zs. zs. zs. zs. zs. release_frame FR ST (bv_unsigned sp). zs.
    all: match goal with |- evt _ _ ?ms => idtac "U1:" ms end.
    apply evt_done. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
  End Sz17.
  Lemma mk_S4 : ltac:(let t := eval cbv delta [mk_S4__stmt] in mk_S4__stmt in exact t).
  Proof using LO NR. intros x1 t0 t1 t2 sA sB a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm jk. ltac2:(SecDiet.SzSec.closeP 'mk_S4__body "vvvvvvvvvvvvvvvvvvvv"). Qed.
End Mk.

(* [comment removed for export] *)
From OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib Require ImgTgtUbsan.
Module TwB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Strings.String.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Tac OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ITree OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Nodes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.Decode OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.SysStep OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.ImgTgtUbsan.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Prelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Monad OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Fmt OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.StdioCore OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Stdio OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Adapter__Spec.StartupModel OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPrelim OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapTypes OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.PcapPure OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Spec.Pcap.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.FileCells OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.AmoStep__Musl.CellsExtra OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrFun OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Musl.FileCells__Musl.StrModel.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.F_syscalls.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strlen.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memcpy.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memchr__S3.F_strrchr.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_memmove.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_lock__S3.StdioKit.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdio_write.TwB OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_strerror__S3.F_stdout_write.TwB.
Import OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.Lib.LiaPin.
(* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac lia ::= pinned_lia.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac mi := match goal with H : mem_inv usegs _ |- _ => exact H end.

Definition open_w_spec__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
    (path : list byte) (errv canary : word) (lo : Z),
  stk usegs m lo (bv_unsigned sp) ->
  bytes_at usegs m (bv_unsigned a0) (path ++ [Z_to_bv 8 0]) ->
  rw_cells usegs m (errno_addr tp) [C4 errv] ->
  rw_cells usegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] ->
  rw_cells usegs m ssp_guard [C8 canary] ->
  mem_inv usegs m ->
  a1 = Z_to_bv 64 577 (* [comment removed for export] *) -> a2 = Z_to_bv 64 384 (* [comment removed for export] *) ->
  ~ In (Z_to_bv 8 0) path ->
  (Namei.path_has_slash path = false \/ path = Uapi.devnull_path) ->   (* [comment removed for export] *)
  (lo <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= errno_addr tp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= bv_unsigned sp - 112 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length path) + 1 <= errno_addr tp \/ errno_addr tp + 4 <= bv_unsigned a0)%Z ->
  (ssp_guard + 8 <= bv_unsigned sp - 112)%Z ->
  (errno_addr tp + 4 <= ssp_guard \/ ssp_guard + 8 <= errno_addr tp)%Z ->
  (got_ssp + 8 <= errno_addr tp \/ errno_addr tp + 4 <= got_ssp)%Z ->
  (164 <= bv_unsigned tp)%Z ->
  impl usegs (at_node usegs) (npeek usegs) (enode (NOpenW path 384) dec_openw)
       (epost (open_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a0) path errv canary lo m))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x18cf8) fc None m (seg_rom usegs)).
Section Sz1.
Variables ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv canary lo : ltac2:(SecDiet.SzSec.tyM 'open_w_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma open_w_spec__body : ltac2:(SecDiet.SzSec.bodyP 'open_w_spec__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros ST SRC ERR GOT SSP MI -> Ha2 NUL NSLASH LO SEP1 SEP2 SEP3 SEP4 SEP5 SEP6 TP.
  unfold got_ssp, ssp_guard in *.
  pose proof (munch_refl [(bv_unsigned sp - 112, bv_unsigned sp); (errno_addr tp, errno_addr tp + 4)]%Z m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (bytes_at_bound _ _ _ _ SRC) as BP. rewrite length_app in BP. cbn [length] in BP.
  apply impl_enode.
  carve_frame 96%nat ST.
  do 18 step.
  if_true. subst a2.
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ ?mm ?A (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: C8 (Z_to_bv 64 384) :: ?rest) =>
    assert (FR' : rw_cells usegs mm A (c0 :: c1 :: c2 :: c3 :: c4 :: C4 (Z_to_bv 64 384) :: C4 (Z_to_bv 64 0) :: rest))
      by (pose proof (proj1 (proj1 FR)) as WF; cbn [cells_wf cell_wf] in WF; eapply (rw_cells_recast mm A _ _ FR); [cbn [cells_wf cell_wf]; (keep_hyps sp tp a0 path junk WF; tauto)| reflexivity| reflexivity]);
    clear FR; rename FR' into FR
  end.
  step.
  all: match goal with |- evt _ _ ?ms => idtac "OW2:" ms end.
  do 8 step. (* [comment removed for export] *) do 8 step. (* [comment removed for export] *)
  step_ecall.
  split. { at_node_solve. }
  intros rsp ans Hdec. apply dec_plain_Some in Hdec.
  destruct ans as [e|fd].
  - destruct Hdec as [-> He]. unfold efferr, eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_errno by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | (keep_hyps sp a0 path lo LO; lia) | (keep_hyps sp tp a0 path SEP1; lia) | (keep_hyps tp a0 path TP; lia) | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_errno_ret in * by lia.
    do 3 step. if_false. do 6 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
  - destruct Hdec as (-> & Hfd & Hrange). apply andb_prop in Hfd as [Hfd3 Hfd]. apply Z.leb_le in Hfd3. apply Z.leb_le in Hfd. unfold eff0. sys_nret.
    do 4 step. if_true. step. rewrite sextw_small by lia. step.
    call_sp sysret_spec; [exact ST | exact ERR | exact MI | (keep_hyps sp a0 path lo LO; lia) | (keep_hyps sp tp a0 path SEP1; lia) | (keep_hyps tp a0 path TP; lia) | ]. rename PC into ST; rename POST into ERR.
    unfold sysret_val, sysret_errno in *. rewrite errno_of_lit in * by lia.
    do 3 step. if_false. step. rewrite sextw_small by lia. do 5 step. release_frame FR ST (bv_unsigned sp).
    unfold open_post, open_ret, open_errno, got_ssp, ssp_guard. sys_finish; lia.
Qed.
End Sz1.
Lemma open_w_spec : ltac:(let t := eval cbv delta [open_w_spec__stmt] in open_w_spec__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m path errv canary lo. ltac2:(SecDiet.SzSec.closeP 'open_w_spec__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

(* [comment removed for export] *)
#[local] Definition b8 (z : Z) : byte := Z_to_bv 8 z.
Definition TMPL : list byte := map b8 TEMPLATE.                                    (* [comment removed for export] *)
Definition SEALED : list byte := map b8 (str "/tmp/libpcap_fuzz_pcap.000000"%string).   (* [comment removed for export] *)
Definition TMPN : list byte := map b8 TMPNAME.                                     (* [comment removed for export] *)
Definition MKSTEMP : Z := 0x182d8.

Lemma TMPL_len : length TMPL = 29%nat. Proof. reflexivity. Qed.
Lemma SEALED_len : length SEALED = 29%nat. Proof. reflexivity. Qed.
Lemma TMPN_len : length TMPN = 24%nat. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition TMPL0 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 88; Z_to_bv 8 0].      (* [comment removed for export] *)
Definition SEALED0 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47; Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 0].  (* [comment removed for export] *)
Definition TMP5 : list byte := [Z_to_bv 8 47; Z_to_bv 8 116; Z_to_bv 8 109; Z_to_bv 8 112; Z_to_bv 8 47].   (* [comment removed for export] *)
Definition TMPN0 : list byte := [Z_to_bv 8 108; Z_to_bv 8 105; Z_to_bv 8 98; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 95; Z_to_bv 8 102; Z_to_bv 8 117; Z_to_bv 8 122; Z_to_bv 8 122; Z_to_bv 8 95; Z_to_bv 8 112; Z_to_bv 8 99; Z_to_bv 8 97; Z_to_bv 8 112; Z_to_bv 8 46; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 48; Z_to_bv 8 0].  (* [comment removed for export] *)
Lemma TMPL0_eq : TMPL ++ [Z_to_bv 8 0] = TMPL0. Proof. vm_compute. reflexivity. Qed.
Lemma TMPL0_len_30 : length TMPL0 = 30%nat. Proof. reflexivity. Qed.
Lemma SEALED0_eq : SEALED ++ [Z_to_bv 8 0] = SEALED0. Proof. vm_compute. reflexivity. Qed.
Lemma TMPN0_eq : TMPN ++ [Z_to_bv 8 0] = TMPN0. Proof. vm_compute. reflexivity. Qed.



(* [comment removed for export] *)
Definition memcpy_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D S N : Z) (src : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + N)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ rw_cells usegs m' D [CB (Z.to_nat N) src] /\ bytes_at usegs m' S src.
Definition memcpy_callw__stmt : Prop := forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (D S N : Z) (src junk : list byte),
  bytes_at usegs m S src -> length src = Z.to_nat N -> rw_cells usegs m D [CB (Z.to_nat N) junk] ->
  (S + N <= D \/ D + N <= S) -> 0 <= N -> 0 <= D -> D + N < 2^64 -> 0 <= S -> S + N < 2^64 -> mem_inv usegs m ->
  evt usegs (memcpy_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D S N src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 S) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x20fa0) fc None m (seg_rom usegs)).
Section Sz10.
Variables ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S N src junk : ltac2:(SecDiet.SzSec.tyM 'memcpy_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv" @ra).
#[using="Type"] Lemma memcpy_callw__body : ltac2:(SecDiet.SzSec.bodyP 'memcpy_callw__stmt "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv").
Proof.
 intros SRC LEN DST SEP HN HD HDN HS HSN MI.
  assert (ED : bv_unsigned (Z_to_bv 64 D : word) = D) by (apply unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S : word) = S) by (apply unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N : word) = N) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memcpy_spec with (junk := junk); rewrite ?ED, ?ES, ?EN; [exact SRC | exact LEN | exact DST | exact SEP | exact MI]. }
  intros ms' PO. unfold memcpy_post, memcpy_postv in *. rewrite ED, ES, EN in PO. exact PO.
Qed.
End Sz10.
Lemma memcpy_callw : ltac:(let t := eval cbv delta [memcpy_callw__stmt] in memcpy_callw__stmt in exact t).
Proof. intros ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m D S N src junk. ltac2:(SecDiet.SzSec.closeP 'memcpy_callw__body "vvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvvv"). Qed.

Definition strrchr_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A c : Z) (str slack : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strrchr_res A c str)) a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp) /\ bytes_at usegs m' A (str ++ Z_to_bv 8 0 :: slack).
Lemma strrchr_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A c : Z) (str slack : list byte) (lo : Z),
  stk usegs m lo (bv_unsigned sp) -> bytes_at usegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> mem_inv usegs m -> lo <= bv_unsigned sp - 32 ->
  (A + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned sp - 32 \/ bv_unsigned sp <= A) ->
  0 <= A < 2^64 -> 0 <= c < 256 ->
  evt usegs (strrchr_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A c str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) (Z_to_bv 64 c) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x218a0) fc None m (seg_rom usegs)).
Proof.
  intros until lo. intros ST STR NONUL PAD MI LO SEP HA HC.
  assert (EA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; lia).
  assert (EC : bv_unsigned (Z_to_bv 64 c : word) = c) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply strrchr_spec; rewrite ?EA, ?EC; [exact ST | exact STR | exact NONUL | exact PAD | exact MI | exact LO | exact SEP]. }
  intros ms' PO. unfold strrchr_post, strrchr_postv in *. rewrite EA, EC, (Z.mod_small c 256) in PO by lia. exact PO.
Qed.

Definition strlen_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (A : Z) (str slack : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (length str))) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ bytes_at usegs m' A (str ++ Z_to_bv 8 0 :: slack).
Lemma strlen_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (A : Z) (str slack : list byte),
  bytes_at usegs m A (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  (- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack) -> mem_inv usegs m -> 0 <= A < 2^64 ->
  evt usegs (strlen_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc A str slack m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x217cc) fc None m (seg_rom usegs)).
Proof.
  intros until slack. intros STR NONUL PAD MI HA.
  assert (EA : bv_unsigned (Z_to_bv 64 A : word) = A) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply strlen_spec; rewrite ?EA; [exact STR | exact NONUL | exact PAD | exact MI]. }
  intros ms' PO. unfold strlen_post, strlen_postv in *. rewrite EA in PO. exact PO.
Qed.

Definition memmove_postv (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (D k N : Z) (bs : list byte) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(D, D + N)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' D (firstn (Z.to_nat N) (skipn (Z.to_nat k) bs) ++ skipn (Z.to_nat N) bs).
Lemma memmove_callw : forall ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (bs : list byte) (D k N : Z),
  u8arr usegs m D bs -> mem_inv usegs m -> 1 <= k -> 0 <= N < 2^62 -> length bs = Z.to_nat (k + N) -> 0 <= D -> D + k < 2^64 ->
  evt usegs (memmove_postv ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc D k N bs m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 D) (Z_to_bv 64 (D + k)) (Z_to_bv 64 N) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x213a4) fc None m (seg_rom usegs)).
Proof.
  intros until N. intros ARR MI HK HN LEN HD HDK.
  assert (ED : bv_unsigned (Z_to_bv 64 D : word) = D) by (apply unsigned_lit; lia).
  assert (EDK : bv_unsigned (Z_to_bv 64 (D + k) : word) = D + k) by (apply unsigned_lit; lia).
  eapply evt_mono. { eapply memmove_spec; rewrite ?ED, ?EDK; [exact ARR | exact MI | reflexivity | reflexivity | exact HK | exact HN | exact LEN]. }
  intros ms' PO. unfold memmove_post, memmove_postv in *. rewrite ED in PO. exact PO.
Qed.

Section Mk.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (NAME lo : Z) (n : nat).
  Hypothesis LO : lo <= bv_unsigned sp - 144.
  Hypothesis GLO : 0x56000 <= lo.
  Hypothesis N0 : 0 < NAME.
  Hypothesis NSEP : NAME + Z.of_nat n <= lo \/ bv_unsigned sp <= NAME.
  Hypothesis NHI : NAME + Z.of_nat n <= 2^47.
  Hypothesis NR : (38 <= n <= 4096)%nat.
  Hypothesis NROM : NAME + Z.of_nat n <= 0x10000 \/ 0x56000 <= NAME.   (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition mk_S1__stmt : Prop := forall (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (m : mem),
    rw_cells usegs m NAME [CB 30 TMPL0; CB (n - 30) rest] ->
    stk usegs m lo (bv_unsigned sp) -> mem_inv usegs m ->
    evt usegs (fun ms' => exists (x1 t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (jk : list byte) (m1 : mem),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 NAME) (Z_to_bv 64 0) (Z_to_bv 64 29) a1' a2' a3' a4' a5' a6' a7'
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x18324) fc None m1 (seg_rom usegs)
        /\ rw_cells usegs m1 (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 32, bv_unsigned sp)] m m1 /\ wmono usegs m m1 /\ mem_inv usegs m1
        /\ stk usegs m1 lo (bv_unsigned sp + -32))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 MKSTEMP) fc None m (seg_rom usegs)).
  Section Sz14.
  Variables t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest m : ltac2:(SecDiet.SzSec.tyM 'mk_S1__stmt "vvvvvvvvvvvvvvvv" @t0).
  Lemma mk_S1__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S1__stmt "vvvvvvvvvvvvvvvv").
  Proof using GLO LO N0 NHI NR NROM NSEP. pin_using (fun (GLO LO N0 NHI NR NROM NSEP : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
 intros BUF ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 32, bv_unsigned sp)] m) as MU. pose proof (wmono_refl usegs m) as WM.
    unfold MKSTEMP.
    carve_frame 32%nat ST.
    zs. zs. zs. zs. zs. zs.
    zs. if_cases K0; zify_cond K0. 1:{ exfalso. rewrite ?Z.mod_small in K0 by lia. lia. }
    zs. zs. if_cases K1; zify_cond K1. 1:{ exfalso. revert K1. cbn. lia. }
    zs.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (STR : bytes_at usegs mm (bv_unsigned (Z_to_bv 64 NAME : word)) (TMPL ++ Z_to_bv 8 0 :: rest)) end.
    { rewrite unsigned_lit by lia.
      pose proof BUF as [[_ HB] _]. cbn [cells_bytes cbytes] in HB. rewrite app_nil_r, <- TMPL0_eq, <- app_assoc in HB. exact HB. }
    zs. call_sp strlen_spec; [exact STR | unfold TMPL, TEMPLATE; cbn; clear; intuition discriminate | | mi | ].
    { rewrite unsigned_lit by lia. rewrite TMPL_len. pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LR & _).
      eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; lia|]. lia. }
    rewrite TMPL_len. zs. zs. if_cases K2; zify_cond K2. 2:{ exfalso. revert K2. rewrite ?unsigned_lit by lia. cbn. lia. }
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact FR|]. split; [exact MU|]. split; [exact WM|]. split; [mi| exact ST].
  Qed.
  End Sz14.
  Lemma mk_S1 : ltac:(let t := eval cbv delta [mk_S1__stmt] in mk_S1__stmt in exact t).
  Proof using GLO LO N0 NHI NR NROM NSEP. intros t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest m. ltac2:(SecDiet.SzSec.closeP 'mk_S1__body "vvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mk_S2__stmt : Prop := forall (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (mm : mem),
    rw_cells usegs mm NAME [CB 30 TMPL0; CB (n - 30) rest] -> mem_inv usegs mm ->
    evt usegs (fun ms' => exists (a4' : word),
        ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0)
                     (Z_to_bv 64 (NAME + 23)) (Z_to_bv 64 0) (Z_to_bv 64 88) (Z_to_bv 64 (NAME + 29)) a4' a5 a6 a7
                     s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x18350) fc None mm (seg_rom usegs))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0) (Z_to_bv 64 29) a1 a2 a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x18324) fc None mm (seg_rom usegs)).
  Section Sz15.
  Variables x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest mm : ltac2:(SecDiet.SzSec.tyM 'mk_S2__stmt "vvvvvvvvvvvvvvvvv" @x1).
  Lemma mk_S2__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S2__stmt "vvvvvvvvvvvvvvvvv").
  Proof using N0 NHI NR. pin_using (fun (N0 NHI NR : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
 intros BUF MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    unfold TMPL0 in BUF.
    zs. zs. zs. replace (NAME + 29 - 0 + -6) with (NAME + 23) by lia. zs. zs. zs.
    (* [comment removed for export] *)
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_true.
    zs. cbn [firstn skipn]. load_post. first [change (zxb (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word) | change ((fun b : byte => Z_to_bv 64 (bv_unsigned b)) (Z_to_bv 8 88)) with (Z_to_bv 64 88 : word)]. zs. if_false. zs. zs. zs. if_false.
    apply evt_done. eexists. cbv delta [mkR]. reflexivity.
  Qed.
  End Sz15.
  Lemma mk_S2 : ltac:(let t := eval cbv delta [mk_S2__stmt] in mk_S2__stmt in exact t).
  Proof using N0 NHI NR. intros x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 rest mm. ltac2:(SecDiet.SzSec.closeP 'mk_S2__body "vvvvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mk_S3__stmt : Prop := forall (x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (rest : list byte) (mm : mem) (jk : list byte),
    rw_cells usegs mm NAME [CB 30 TMPL0; CB (n - 30) rest] ->
    rw_cells usegs mm (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
    stk usegs mm lo (bv_unsigned sp + -32) -> mem_inv usegs mm ->
    evt usegs (fun ms' => exists (x1' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        ms' = MS (mkR x1' (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0' t1' t2' (Z_to_bv 64 NAME) (Z_to_bv 64 (NAME + 5))
                     a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                 F (Z_to_bv 64 0x18388) fc None m' (seg_rom usegs)
        /\ rw_cells usegs m' NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]
        /\ rw_cells usegs m' (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra]
        /\ munch [(bv_unsigned sp - 64, bv_unsigned sp - 32); (NAME, NAME + 30)] mm m' /\ wmono usegs mm m' /\ mem_inv usegs m'
        /\ stk usegs m' lo (bv_unsigned sp + -32))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) (Z_to_bv 64 0)
               (Z_to_bv 64 (NAME + 23)) (Z_to_bv 64 0) (Z_to_bv 64 88) (Z_to_bv 64 (NAME + 29)) a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x18350) fc None mm (seg_rom usegs)).
  Section Sz16.
  Variables x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 rest mm jk : ltac2:(SecDiet.SzSec.tyM 'mk_S3__stmt "vvvvvvvvvvvvvvv" @x1).
  Lemma mk_S3__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S3__stmt "vvvvvvvvvvvvvvv").
  Proof using GLO LO N0 NHI NR NROM NSEP. pin_using (fun (GLO LO N0 NHI NR NROM NSEP : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
 intros BUF FR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp - 32); (NAME, NAME + 30)] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    pose proof (proj1 (proj1 BUF)) as WF. cbn [cells_wf cell_wf] in WF. destruct WF as (_ & LR & _).
    (* [comment removed for export] *)
    pose proof (rw_cells_split_CB usegs mm NAME [] 30 TMPL0 [CB (n - 30) rest] [23%nat; 6%nat; 1%nat] BUF eq_refl) as B4.
    cbn [app mk_CB_cells] in B4. unfold TMPL0 in B4. cbn [firstn skipn] in B4. clear BUF.
    apply (proj1 (rw_cells_app usegs mm NAME [_] _)) in B4 as [P1 B4]. apply (proj1 (rw_cells_app usegs mm _ [_] _)) in B4 as [DST B4].
    cbn [cells_size csize Nat.add] in DST, B4.
    replace (NAME + Z.of_nat 23) with (NAME + 23) in DST by lia. replace (NAME + Z.of_nat 23 + Z.of_nat 6) with (NAME + 29) in B4 by lia.
    zs. zs.
    zs. call_sp OSSVerify.Proofs.libpcap.fuzz_pcap.lib.E2.S3.F_memmove__S3.F_fopen.TwB.memset_callw; [exact DST | (keep_hyps n rest; lia) | (keep_hyps NAME n rest N0; lia) | (keep_hyps NAME n rest NHI; lia) | (keep_hyps n rest; lia) | mi |].
    match goal with H : rw_cells usegs _ (NAME + 23) [CB _ (repeat _ _)] |- _ => rename H into SEALC end.
    change (Z.to_nat 6) with 6%nat in SEALC.
    replace (repeat (Z_to_bv 8 (48 mod 256)) 6) with (map b8 SEAL) in SEALC by (vm_compute; reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m2 end.
    (* [comment removed for export] *)
    assert (STR2 : bytes_at usegs m2 NAME (SEALED ++ Z_to_bv 8 0 :: rest)).
    { pose proof (proj2 (proj1 P1)) as X1. pose proof (proj2 (proj1 SEALC)) as X2. pose proof (proj2 (proj1 B4)) as X3.
      cbn [cells_bytes cbytes app] in X1, X2, X3. try rewrite app_nil_r in X1. try rewrite app_nil_r in X2.
      assert (E : SEALED ++ Z_to_bv 8 0 :: rest = (firstn 23 TMPL0 ++ map b8 SEAL) ++ (Z_to_bv 8 0 :: rest)).
      { cbv -[Z_to_bv]. reflexivity. }
      rewrite E. apply (proj2 (bytes_at_app _ _ _ _ _)). split.
      - apply (proj2 (bytes_at_app _ _ _ _ _)). split; [exact X1|].
        match goal with |- bytes_at _ _ ?a _ => replace a with (NAME + 23) by (cbn [length firstn app map TMPL0 Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Nat2Z.inj_succ; cbn; lia) end. exact X2.
      - match goal with |- bytes_at _ _ ?a _ => replace a with (NAME + 29) by (rewrite length_app, length_firstn, length_map; cbn; lia) end.
        rewrite app_nil_r in X3. exact X3. }
    (* [comment removed for export] *)
    zs. zs. zs.
    call_sp strrchr_callw; [exact ST | exact STR2 | unfold SEALED; cbn; clear; intuition discriminate | rewrite SEALED_len; eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; (keep_hyps n rest; lia)| (keep_hyps n rest NRZ LR; lia)]
                          | mi | (keep_hyps sp lo n rest LO; lia) | rewrite SEALED_len; (keep_hyps sp NAME lo n rest LO NSEP LR; lia) | (keep_hyps NAME n rest N0 NHI; lia) | (keep_hyps n rest; lia) | ].
    assert (LB : last_byte 47 (SEALED ++ [Z_to_bv 8 0]) = Some 4%nat) by (vm_compute; reflexivity).
    unfold strrchr_res, memrchr_res. rewrite LB. change (NAME + Z.of_nat 4) with (NAME + 4).
    zs. if_cases KZ; zify_cond KZ. 1:{ exfalso. rewrite ?Z.mod_small in KZ by lia. lia. }
    zs. zs.
    replace (NAME + 4 + 1) with (NAME + 5) by lia.
    (* [comment removed for export] *)
    match goal with H : bytes_at usegs _ NAME (SEALED ++ _) |- _ => rename H into STR3 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m3 end.
    assert (STR5 : bytes_at usegs m3 (NAME + 5) (TMPN ++ Z_to_bv 8 0 :: rest)).
    { assert (E5 : SEALED ++ Z_to_bv 8 0 :: rest = TMP5 ++ (TMPN ++ Z_to_bv 8 0 :: rest)) by (cbv -[Z_to_bv]; reflexivity).
      rewrite E5 in STR3. apply (proj1 (bytes_at_app _ _ _ _ _)) in STR3 as [_ STR3]. cbn [length TMP5 Z.of_nat Pos.of_succ_nat Pos.succ] in STR3.
      exact STR3. }
    zs. call_sp strlen_callw; [exact STR5 | unfold TMPN, TMPNAME; cbn; clear; intuition discriminate | rewrite TMPN_len; eapply Z.le_trans; [apply Z.lt_le_incl, Z.mod_pos_bound; (keep_hyps n rest; lia)| (keep_hyps n rest NRZ LR; lia)] | mi | (keep_hyps NAME n rest N0 NHI; lia) | ].
    rewrite TMPN_len.
    zs. zs. zs. replace (Z.of_nat 24 + 1) with 25 by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m4 end.
    match goal with H : rw_cells usegs m4 NAME [CB 23 _] |- _ => rename H into Q1 end.
    match goal with H : rw_cells usegs m4 (NAME + 23) _ |- _ => rename H into Q2 end.
    match goal with H : rw_cells usegs m4 (NAME + 29) _ |- _ => rename H into Q3 end.
    apply (proj1 (rw_cells_app usegs m4 (NAME + 29) [_] _)) in Q3 as [Q3 RESTC]. cbn [cells_size csize Nat.add] in RESTC.
    replace (NAME + 29 + Z.of_nat 1) with (NAME + 30) in RESTC by lia.
    assert (J1 : rw_cells usegs m4 (NAME + 23) ([CB 6 (map b8 SEAL)] ++ [CB 1 [Z_to_bv 8 0]])).
    { apply (proj2 (rw_cells_app usegs m4 (NAME + 23) _ _)). split; [exact Q2|]. cbn [cells_size csize Nat.add]. replace (NAME + 23 + Z.of_nat 6) with (NAME + 29) by lia. exact Q3. }
    assert (J2 : rw_cells usegs m4 NAME ([CB 23 (firstn 23 TMPL0)] ++ ([CB 6 (map b8 SEAL)] ++ [CB 1 [Z_to_bv 8 0]]))).
    { apply (proj2 (rw_cells_app usegs m4 NAME _ _)). split; [unfold TMPL0; cbn [firstn]; exact Q1|]. cbn [cells_size csize Nat.add]. replace (NAME + Z.of_nat 23) with (NAME + 23) by lia. exact J1. }
    assert (B30 : rw_cells usegs m4 NAME [CB 30 SEALED0]).
    { eapply (rw_cells_recast m4 NAME _ _ J2); [cbn; split; [reflexivity| exact I] | cbv -[Z_to_bv]; reflexivity | reflexivity]. }
    clear Q1 Q2 Q3 J1 J2.
    pose proof (u8arr_of_rw_cells usegs m4 NAME 30 SEALED0 B30) as ARR.
    zs. call_sp memmove_callw; [exact ARR | mi | (keep_hyps n rest; lia) | (keep_hyps n rest; lia) | reflexivity | (keep_hyps NAME n rest N0; lia) | (keep_hyps NAME n rest NHI; lia) | ].
    match goal with H : u8arr usegs _ NAME _ |- _ => rename H into ARR2 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename mq into m5 end.
    pose proof (rw_cells_of_u8arr usegs m5 NAME _ ARR2) as B30'.
    assert (B30n : rw_cells usegs m5 NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0)]).
    { eapply (rw_cells_recast m5 NAME _ _ B30'); [cbn; split; [reflexivity| exact I] | cbv -[Z_to_bv]; reflexivity | reflexivity]. }
    match goal with H : rw_cells usegs m5 (NAME + 30) _ |- _ => rename H into RESTC5 end.
    assert (BUF5 : rw_cells usegs m5 NAME [CB 30 (TMPN0 ++ skipn 25 SEALED0); CB (n - 30) rest]).
    { apply (proj2 (rw_cells_app usegs m5 NAME [_] [_])). split; [exact B30n|]. cbn [cells_size csize Nat.add]. replace (NAME + Z.of_nat 30) with (NAME + 30) by lia. exact RESTC5. }
    apply evt_done. repeat (lazymatch goal with |- ex _ => eexists end).
    split; [cbv delta [mkR]; reflexivity|]. split; [exact BUF5|].
    split; [match goal with H : rw_cells usegs m5 (bv_unsigned sp + -32) _ |- _ => exact H end|].
    split; [exact MU|]. split; [exact WM|]. split; [mi|].
    match goal with H : stk usegs m5 lo _ |- _ => exact H end.
  Qed.
  End Sz16.
  Lemma mk_S3 : ltac:(let t := eval cbv delta [mk_S3__stmt] in mk_S3__stmt in exact t).
  Proof using GLO LO N0 NHI NR NROM NSEP. intros x1 t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 rest mm jk. ltac2:(SecDiet.SzSec.closeP 'mk_S3__body "vvvvvvvvvvvvvvv"). Qed.

  (* [comment removed for export] *)
  Definition mk_S4__stmt : Prop := forall (x1 t0 t1 t2 sA sB a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mm : mem) (jk : list byte),
    rw_cells usegs mm (bv_unsigned sp + -32) [CB 8 jk; C8 s1; C8 s0; C8 ra] ->
    stk usegs mm lo (bv_unsigned sp + -32) -> mem_inv usegs mm ->
    evt usegs (fun ms' =>
        ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 NAME) (Z_to_bv 64 577) (Z_to_bv 64 384) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 0x18cf8) fc None mm (seg_rom usegs)
        /\ stk usegs mm lo (bv_unsigned sp))
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 NAME) sB a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x18388) fc None mm (seg_rom usegs)).
  Section Sz17.
  Variables x1 t0 t1 t2 sA sB a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm jk : ltac2:(SecDiet.SzSec.tyM 'mk_S4__stmt "vvvvvvvvvvvvvvvvvvvv" @x1).
  Lemma mk_S4__body : ltac2:(SecDiet.SzSec.bodyP 'mk_S4__stmt "vvvvvvvvvvvvvvvvvvvv").
  Proof using LO NR. pin_using (fun (LO NR : unit) => tt). (* [comment removed for export] *) assert (NRZ : (38 <= Z.of_nat n <= 4096)%Z) by (clear - NR; lia). clear NR.
 intros FR ST MI.
    pose proof (bv_unsigned_in_range 64 sp) as SPHI. unfold bv_modulus in SPHI. cbn in SPHI.
    pose proof (munch_refl [] mm) as MU. pose proof (wmono_refl usegs mm) as WM.
    zs. zs. zs. zs. zs. zs. zs. release_frame FR ST (bv_unsigned sp). zs.
    all: match goal with |- evt _ _ ?ms => idtac "U1:" ms end.
    apply evt_done. split; [cbv delta [mkR]; reflexivity| exact ST].
  Qed.
  End Sz17.
  Lemma mk_S4 : ltac:(let t := eval cbv delta [mk_S4__stmt] in mk_S4__stmt in exact t).
  Proof using LO NR. intros x1 t0 t1 t2 sA sB a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 mm jk. ltac2:(SecDiet.SzSec.closeP 'mk_S4__body "vvvvvvvvvvvvvvvvvvvv"). Qed.
End Mk.
End TwB.
End F_mkstemp.
