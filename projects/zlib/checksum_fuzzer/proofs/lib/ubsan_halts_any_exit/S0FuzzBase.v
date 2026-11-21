(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import RunCtx.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require RunHit.  (* the run's first match *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.World Require Import Src_zlib_checksum_fuzzer_repro.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk Frame RefMemcpyLib AgentLib SumWalkTac
  FuzzLib FuzzZ.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit Require Import LiaFast.
From OSSVerify.Proofs.zlib.checksum_fuzzer.lib.ubsan_halts_any_exit.cks Require Import CkTables.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation RSEGS := Src_zlib_checksum_fuzzer_repro.M.loaded_segments.


Definition RO_LO : Z := 0x10554.
Definition RO_HI : Z := 0x119e8.
Definition RO_N : nat := Z.to_nat 5268.
Definition CTAB : Z := 0x10554.
Definition BTAB : Z := 0x10954.
Definition X2NT : Z := 0x11954.
Definition AMAG : Z := 0x119e0.

Definition img_ok (m : word -> option byte) : Prop :=
  forall i, (RO_LO <= i < RO_HI)%Z -> m (Z_to_bv 64 i) = None.

Lemma img_ok_of_hyp : forall m,
  (forall j, (0 <= j < 0x1494)%Z -> m (Z_to_bv 64 (0x10554 + j)) = None) -> img_ok m.
Proof.
  intros m H i Hi. unfold RO_LO, RO_HI in Hi.
  replace i with (0x10554 + (i - 0x10554))%Z by lia. apply H. lia.
Qed.

Lemma wview_ro_none {RCa1 : RunCtx}  : forall m x, (0x10000 <= x < 0x13000)%Z ->
  m (Z_to_bv 64 x) = None -> wview (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 x) = None.
Proof.
  intros m x Hx Hm. unfold wview. rewrite Hm. rewrite u64_lit by lia.
  (* the hit is computed on the image's list; over the run the image answers first *)
  assert (E : exists s, find_segment M.loaded_segments x 1 = Some s /\ seg_writable s = false).
  { cbn [find_segment M.loaded_segments Src_zlib_checksum_fuzzer_repro_loaded_segments seg_base seg_size
         Src_zlib_checksum_fuzzer_repro_segment_000 Z.of_N].
    replace ((65536 <=? x)%Z && (x + 1 <=? 65536 + 12288)%Z)%bool with true
      by (symmetry; apply andb_true_intro; split; apply Z.leb_le; lia).
    eexists; split; reflexivity. }
  destruct E as (s & E & W).
  unfold LinuxProcessSemantics.LinuxProcessSem.Run.run_segments. rewrite (RunHit.find_segment_app_hit _ _ _ _ _ E).
  rewrite W. reflexivity.
Qed.

Lemma store_ok_off_ro {RCa1 : RunCtx}  : forall m lo (N : nat),
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 lo) N = true -> (0 <= lo)%Z -> (lo + Z.of_nat N <= 2 ^ 64)%Z ->
  (0 < Z.of_nat N)%Z ->
  img_ok m -> (RO_HI <= lo \/ lo + Z.of_nat N <= RO_LO)%Z.
Proof.
  intros m lo N Hok Hlo Hhi HN Himg.
  destruct (Z.le_gt_cases RO_HI lo) as [|H1]; [left; assumption|].
  destruct (Z.le_gt_cases (lo + Z.of_nat N) RO_LO) as [|H2]; [right; assumption|].
  exfalso. unfold RO_LO, RO_HI in *.
  set (x := Z.max lo 0x10554).
  assert (Hx1 : (lo <= x < lo + Z.of_nat N)%Z) by (subst x; lia).
  assert (Hx2 : (0x10554 <= x < 0x119e8)%Z) by (subst x; lia).
  apply (store_ok_all (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m N (Z_to_bv 64 lo) ltac:(rewrite u64_lit by lia; lia) Hok (Z_to_bv 64 x)).
  - rewrite !u64_lit by lia. lia.
  - apply wview_ro_none; [lia|]. apply Himg. unfold RO_LO, RO_HI. lia.
Qed.

Lemma img_ok_wbytes : forall m (wa : word) bs,
  img_ok m ->
  (bv_unsigned wa + Z.of_nat (length bs) <= RO_LO \/ RO_HI <= bv_unsigned wa)%Z ->
  (bv_unsigned wa + Z.of_nat (length bs) <= 2 ^ 64)%Z ->
  img_ok (wbytes m wa bs).
Proof.
  intros m wa bs Hi Hout Hnw i Hr. unfold RO_LO, RO_HI in *.
  rewrite wbytes_outside; [apply Hi; exact Hr | | exact Hnw].
  unfold in_rng. rewrite u64_lit by lia. lia.
Qed.


Definition ro_bytes {RCa1 : RunCtx}  : list byte :=
  match rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 RO_LO) RO_N return list byte with Some bs => bs | None => @nil byte end.

Lemma rdn_ro_rom {RCa1 : RunCtx}  : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (fun _ => None) (Z_to_bv 64 RO_LO) RO_N = Some ro_bytes.
Proof. vm_compute. reflexivity. Qed.


Lemma rdn_ro {RCa1 : RunCtx}  : forall m, img_ok m -> rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 RO_LO) RO_N = Some ro_bytes.
Proof.
  intros m Hm. rewrite (rdn_img (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m RO_LO RO_N RO_LO RO_HI Hm).
  - apply rdn_ro_rom.
  - unfold RO_LO; lia.
  - change (Z.of_nat RO_N) with 5268%Z. unfold RO_LO, RO_HI; lia.
  - unfold RO_LO; lia.
  - unfold RO_HI; lia.
Qed.

Lemma ro_read_sub {RCa1 : RunCtx}  : forall m (off : Z) (k : nat), img_ok m -> (0 <= off)%Z -> (off + Z.of_nat k <= 5268)%Z ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (RO_LO + off)) k = Some (sub ro_bytes (Z.to_nat off) k).
Proof.
  intros m off k Hm Hoff Hk.
  replace (Z_to_bv 64 (RO_LO + off)) with (at_ (Z_to_bv 64 RO_LO) (Z.of_nat (Z.to_nat off)))
    by (unfold at_, RO_LO; rewrite u64_lit by lia; f_equal; lia).
  apply (rdn_sub (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m RO_N); [apply rdn_ro; exact Hm | unfold RO_N; lia].
Qed.


Definition ctab_bs {RCa1 : RunCtx}  (i : Z) : list byte := sub ro_bytes (Z.to_nat (4 * i)) 4.
Definition btab_bs {RCa1 : RunCtx}  (k i : Z) : list byte := sub ro_bytes (Z.to_nat (1024 + 1024 * k + 4 * i)) 4.
Definition x2n_bs {RCa1 : RunCtx}  (i : Z) : list byte := sub ro_bytes (Z.to_nat (5120 + 4 * i)) 4.
Definition amag_bs {RCa1 : RunCtx}  : list byte := sub ro_bytes (Z.to_nat 5260) 8.

Lemma rd_ctab {RCa1 : RunCtx}  : forall m i, img_ok m -> 0 <= i < 256 ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (CTAB + 4 * i)) 4 = Some (ctab_bs i).
Proof.
  intros m i Hm Hi. unfold ctab_bs.
  replace (CTAB + 4 * i) with (RO_LO + 4 * i) by reflexivity.
  apply ro_read_sub; [exact Hm | lia | change (Z.of_nat 4) with 4; lia].
Qed.

Lemma rd_btab {RCa1 : RunCtx}  : forall m k i, img_ok m -> 0 <= k < 4 -> 0 <= i < 256 ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (BTAB + 1024 * k + 4 * i)) 4 = Some (btab_bs k i).
Proof.
  intros m k i Hm Hk Hi. unfold btab_bs.
  replace (BTAB + 1024 * k + 4 * i) with (RO_LO + (1024 + 1024 * k + 4 * i)) by (unfold BTAB, RO_LO; lia).
  apply ro_read_sub; [exact Hm | lia | change (Z.of_nat 4) with 4; lia].
Qed.

Lemma rd_x2n {RCa1 : RunCtx}  : forall m i, img_ok m -> 0 <= i < 32 ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (X2NT + 4 * i)) 4 = Some (x2n_bs i).
Proof.
  intros m i Hm Hi. unfold x2n_bs.
  replace (X2NT + 4 * i) with (RO_LO + (5120 + 4 * i)) by (unfold X2NT, RO_LO; lia).
  apply ro_read_sub; [exact Hm | lia | change (Z.of_nat 4) with 4; lia].
Qed.

Lemma rd_amag {RCa1 : RunCtx}  : forall m, img_ok m ->
  rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 AMAG) 8 = Some amag_bs.
Proof.
  intros m Hm. unfold amag_bs.
  replace AMAG with (RO_LO + 5260) by reflexivity.
  rewrite (ro_read_sub m 5260 8 Hm ltac:(lia) ltac:(change (Z.of_nat 8) with 8; lia)). reflexivity.
Qed.

Definition ctab_ok {RCa1 : RunCtx}  (i : Z) : bool := (bytes_le_to_Z (ctab_bs i) =? ctab i)%Z.
Definition btab_ok {RCa1 : RunCtx}  (k : Z) (i : Z) : bool := (bytes_le_to_Z (btab_bs k i) =? btab k i)%Z.
Definition x2n_ok {RCa1 : RunCtx}  (i : Z) : bool := (bytes_le_to_Z (x2n_bs i) =? x2n i)%Z.

Lemma ctab_bs_val {RCa1 : RunCtx}  : forall i, 0 <= i < 256 -> bytes_le_to_Z (ctab_bs i) = ctab i.
Proof.
  intros i Hi. apply Z.eqb_eq. apply (zallN_spec 256%N ctab_ok); [|exact Hi].
  vm_compute. reflexivity.
Qed.

Lemma btab_bs_val {RCa1 : RunCtx}  : forall k i, 0 <= k < 4 -> 0 <= i < 256 -> bytes_le_to_Z (btab_bs k i) = btab k i.
Proof.
  intros k i Hk Hi.
  assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  destruct E as [-> | [-> | [-> | ->]]]; apply Z.eqb_eq.
  - apply (zallN_spec 256%N (btab_ok 0)); [vm_compute; reflexivity | exact Hi].
  - apply (zallN_spec 256%N (btab_ok 1)); [vm_compute; reflexivity | exact Hi].
  - apply (zallN_spec 256%N (btab_ok 2)); [vm_compute; reflexivity | exact Hi].
  - apply (zallN_spec 256%N (btab_ok 3)); [vm_compute; reflexivity | exact Hi].
Qed.

Lemma x2n_bs_val {RCa1 : RunCtx}  : forall i, 0 <= i < 32 -> bytes_le_to_Z (x2n_bs i) = x2n i.
Proof.
  intros i Hi. apply Z.eqb_eq. apply (zallN_spec 32%N x2n_ok); [|exact Hi].
  vm_compute. reflexivity.
Qed.

Lemma amag_bs_val {RCa1 : RunCtx}  : bytes_le_to_Z amag_bs = AMAGIC.
Proof. vm_compute. reflexivity. Qed.

Definition u32_ok (f : Z -> Z) (i : Z) : bool := ((0 <=? f i) && (f i <? 4294967296))%Z%bool.

Lemma ctab_range : forall i, 0 <= i < 256 -> 0 <= ctab i < two32.
Proof.
  intros i Hi. pose proof (zallN_spec 256%N (u32_ok ctab) ltac:(vm_compute; reflexivity) i Hi) as H.
  unfold u32_ok in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Lemma btab_range : forall k i, 0 <= k < 4 -> 0 <= i < 256 -> 0 <= btab k i < two32.
Proof.
  intros k i Hk Hi.
  assert (E : k = 0 \/ k = 1 \/ k = 2 \/ k = 3) by lia.
  assert (G : forall kk, zall (N.to_nat 256) (u32_ok (btab kk)) 0 = true -> 0 <= btab kk i < two32).
  { intros kk Hz. pose proof (zallN_spec 256%N (u32_ok (btab kk)) Hz i Hi) as H.
    unfold u32_ok in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  destruct E as [-> | [-> | [-> | ->]]]; apply G; vm_compute; reflexivity.
Qed.

Lemma x2n_range : forall i, 0 <= i < 32 -> 0 <= x2n i < two32.
Proof.
  intros i Hi. pose proof (zallN_spec 32%N (u32_ok x2n) ltac:(vm_compute; reflexivity) i Hi) as H.
  unfold u32_ok in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.

Definition nz32_ok (f : Z -> Z) (i : Z) : bool := negb (f i mod 4294967296 =? 0)%Z.

Lemma x2n_nz : forall i, 0 <= i < 32 -> x2n i mod two32 <> 0.
Proof.
  intros i Hi. pose proof (zallN_spec 32%N (nz32_ok x2n) ltac:(vm_compute; reflexivity) i Hi) as H.
  unfold nz32_ok in H. apply negb_true_iff in H. apply Z.eqb_neq in H. exact H.
Qed.

Lemma ctab_bs_v {RCa1 : RunCtx}  : forall i, 0 <= i < 256 -> bytes_le_to_Z (ctab_bs i) = bv_unsigned (Z_to_bv 64 (ctab i)).
Proof. intros i Hi. rewrite ctab_bs_val by lia. pose proof (ctab_range i Hi). rewrite u64_lit by lia. reflexivity. Qed.

Lemma btab_bs_v {RCa1 : RunCtx}  : forall k i, 0 <= k < 4 -> 0 <= i < 256 ->
  bytes_le_to_Z (btab_bs k i) = bv_unsigned (Z_to_bv 64 (btab k i)).
Proof. intros k i Hk Hi. rewrite btab_bs_val by lia. pose proof (btab_range k i Hk Hi). rewrite u64_lit by lia. reflexivity. Qed.

Lemma x2n_bs_v {RCa1 : RunCtx}  : forall i, 0 <= i < 32 -> bytes_le_to_Z (x2n_bs i) = bv_unsigned (Z_to_bv 64 (x2n i)).
Proof. intros i Hi. rewrite x2n_bs_val by lia. pose proof (x2n_range i Hi). rewrite u64_lit by lia. reflexivity. Qed.

Lemma amag_bs_v {RCa1 : RunCtx}  : bytes_le_to_Z amag_bs = bv_unsigned (Z_to_bv 64 AMAGIC).
Proof. rewrite amag_bs_val. reflexivity. Qed.


Definition FR : Z := 192.

Definition FRR (sp : word) : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - FR), FR)].

Lemma stk_ok8 {RCa1 : RunCtx}  : forall (mem m : word -> option byte) (sp : word) (z : Z),
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - FR)) (Z.to_nat FR) = true ->
  (FR <= bv_unsigned sp)%Z -> mem_grows mem m ->
  (bv_unsigned sp - FR <= z)%Z -> (z + 8 <= bv_unsigned sp)%Z ->
  store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 z) 8 = true.
Proof.
  intros mem m sp z Hstk Hsp Hg Hlo Hhi. pose proof (u64_range sp). unfold FR in *.
  eapply store_ok_mono; [exact Hg|].
  eapply (store_ok_sub (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - 192)) _ 192 8);
    [u_norm; lia | exact Hstk | u_norm; lia
    | u_norm; change (Z.of_nat 8) with 8%Z; change (Z.of_nat 192) with 192%Z; lia].
Qed.

Lemma fm_w8 : forall (mem m : word -> option byte) (sp : word) (z : Z) (v : word),
  (FR <= bv_unsigned sp)%Z -> frame_mod mem m (FRR sp) ->
  (bv_unsigned sp - FR <= z)%Z -> (z + 8 <= bv_unsigned sp)%Z ->
  frame_mod mem (wbytes m (Z_to_bv 64 z) (word_to_le_bytes 8 v)) (FRR sp).
Proof.
  intros mem m sp z v Hsp Hf Hlo Hhi. pose proof (u64_range sp). unfold FR in *.
  eapply frame_mod_trans_same; [exact Hf|].
  eapply frame_mod_weaken;
    [| apply frame_mod_wbytes; rewrite lenW8; change (Z.of_nat 8) with 8%Z; u_norm; lia].
  intros a [Ha _]. split; [|exact I]. rewrite lenW8. change (Z.of_nat 8) with 8%Z.
  intros Hin. apply Ha. unfold FRR, FR, in_rng in *. revert Hin. u_norm. lia.
Qed.

Record fzH {RCa1 : RunCtx}  (mem : word -> option byte) (sp data : word) (n : Z) : Prop := FZH {
  Fn    : (1 <= n <= 1048576)%Z;
  Fdata : (1 <= bv_unsigned data)%Z;
  Fnw   : (bv_unsigned data + n < 2 ^ 64)%Z;
  Fsp   : (FR <= bv_unsigned sp)%Z;
  Frd   : forall i, (0 <= i < n)%Z -> exists b, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned data + i)) 1 = Some [b];
  Fstk  : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) mem (Z_to_bv 64 (bv_unsigned sp - FR)) (Z.to_nat FR) = true;
  Fimg  : img_ok mem }.
Arguments FZH {RCa1}.

Section FZ.
Context {RCa1 : RunCtx}.
  Variables (mem : word -> option byte) (sp data : word) (n : Z).
  Hypothesis H : fzH mem sp data n.

  Let usp := bv_unsigned sp.
  Let udata := bv_unsigned data.





  Lemma frame_off_ro : (RO_HI <= usp - FR)%Z \/ (usp <= RO_LO)%Z.
  Proof.
    destruct H. pose proof (u64_range sp).
    destruct (store_ok_off_ro mem (bv_unsigned sp - FR) (Z.to_nat FR) Fstk0 ltac:(unfold FR in *; lia)
                ltac:(unfold FR in *; lia) ltac:(unfold FR; lia) Fimg0); unfold FR in *; subst usp; lia.
  Qed.



End FZ.
