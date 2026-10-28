(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.openssl.pem.images Require Import Asan.
From Ltac2 Require Import Ltac2.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Common Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanHexScan AsanHexZero CertRefl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations.
Import AX2.
Open Scope Z_scope.

Definition A_SEGS : list Segment := Asan.M.loaded_segments.
Definition A_PH : PhdrInfo := Asan.M.phdrs.

(* [comment removed for export] *)
Definition A_ENTRY   : Z := 0x199a18.
Definition A_IMG_LO  : Z := 0x10000.
Definition A_IMG_HI  : Z := 0xbc6000.     (* [comment removed for export] *)
Definition A_TEXT_LO : Z := 0x199000.
Definition A_TEXT_HI : Z := 0x52e000.
Definition A_TEXT_N  : nat := 939008.     (* [comment removed for export] *)
Definition A_RW_LO   : Z := 0x52e000.     (* [comment removed for export] *)
Definition A_RW_HI   : Z := 0xbc6000.
Definition A_PH_ADDR : Z := 0x10040.
Definition A_PH_ENT  : Z := 56.
Definition A_PH_NUM  : Z := 11.

Lemma A_entry_eq : Z.of_N Asan.M.init_pc = A_ENTRY.
Proof. reflexivity. Qed.
Lemma A_phdrs_eq : A_PH = {| ph_addr := 0x10040%N; ph_ent := 56%N; ph_num := 11%N |}.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition A_ITAB : itab := mk_itab A_SEGS A_TEXT_LO A_TEXT_N.

Lemma A_IT_ok : itab_sound A_SEGS A_ITAB.
Proof. apply mk_itab_sound. Qed.

(* [comment removed for export] *)
Lemma A_segs_eq : A_SEGS = [Asan_segment_000; Asan_segment_001;
                            Asan_segment_002; Asan_segment_003].
Proof. reflexivity. Qed.

Lemma A_wx : wx_segs_nowrap A_SEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition A_segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma A_find_segment1_none_outside : forall segs lo hi x,
  A_segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [A_segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma A_segs_in_hull : A_segs_in_hull_b A_SEGS A_IMG_LO A_IMG_HI = true.
Proof. vm_compute. reflexivity. Qed.

Lemma A_outside_hull : forall x, (x < A_IMG_LO \/ A_IMG_HI <= x) -> find_segment A_SEGS x 1 = None.
Proof. intros x Hx. exact (A_find_segment1_none_outside A_SEGS A_IMG_LO A_IMG_HI x A_segs_in_hull Hx). Qed.

(* [comment removed for export] *)
Lemma A_res_eq : segments_reserved A_SEGS
  = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x189000); (Z_to_bv 64 0x199000, Z_to_bv 64 0x395000); (Z_to_bv 64 0x52e000, Z_to_bv 64 0x79000); (Z_to_bv 64 0x5a7000, Z_to_bv 64 0x61f000)].
Proof. vm_compute. reflexivity. Qed.

Lemma A_res_len : length (segments_reserved A_SEGS) = 4%nat.
Proof. rewrite A_res_eq. reflexivity. Qed.

Lemma A_res_hull : Forall (fun iv => A_IMG_LO <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= A_IMG_HI)
                           (segments_reserved A_SEGS).
Proof.
  rewrite A_res_eq. unfold A_IMG_LO, A_IMG_HI.
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma A_res_sizes : fold_right (fun iv acc => bv_unsigned (snd iv) + acc) 0 (segments_reserved A_SEGS) = 0xbb6000.
Proof. rewrite A_res_eq. cbn [fold_right snd]. rewrite ?u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma A_hex2 : scanN Asan_seg_bytes_002 64 0 495616 = true.
Proof. ltac2:(cert_refl_vm constr:(true)). Qed.
Lemma A_hex3 : scanN Asan_seg_bytes_003 64 0 6418432 = true.
Proof. (* [comment removed for export] *)
  apply (scanN_prefix_zwin Asan_seg_bytes_003 798720 6418432 (Uint63.of_Z 1597440) (Uint63.of_Z 11239424)).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.
Lemma A_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 495616%N.
Proof. vm_compute. reflexivity. Qed.
Lemma A_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 6418432%N.
Proof. vm_compute. reflexivity. Qed.

Lemma A_rw_window : forall m (x : word),
  A_RW_LO <= bv_unsigned x < A_RW_HI -> wview A_SEGS m x <> None.
Proof.
  unfold A_RW_LO, A_RW_HI. intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment A_SEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite A_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 495616); [exact A_hex2 | rewrite A_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 6418432); [exact A_hex3 | rewrite A_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x5a7000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
        [rewrite A_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
        [rewrite A_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma A_ro_below_rw : forall seg, In seg A_SEGS -> seg_writable seg = true -> A_RW_LO <= Z.of_N (seg_base seg).
Proof.
  intros seg Hin Hw. rewrite A_segs_eq in Hin. unfold A_RW_LO.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hw |- *; try discriminate; lia.
Qed.
