(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.openssl.hashtable.images Require Import Asan.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.hashtable.lib Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanHexScan CertRefl.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2.
Open Scope Z_scope.

Definition HASEGS : list Segment := Asan.M.loaded_segments.
Definition HAPH : PhdrInfo := Asan.M.phdrs.

(* [comment removed for export] *)
Definition HA_ENTRY   : Z := 0x19a08c.
Definition HA_IMG_LO  : Z := 0x10000.
Definition HA_IMG_HI  : Z := 0xbc8000.     (* [comment removed for export] *)
Definition HA_TEXT_LO : Z := 0x19a000.
Definition HA_TEXT_HI : Z := 0x530000.
Definition HA_TEXT_N  : nat := 940032.     (* [comment removed for export] *)
Definition HA_RW_LO   : Z := 0x530000.     (* [comment removed for export] *)
Definition HA_RW_HI   : Z := 0xbc8000.
Definition HA_PH_ADDR : Z := 0x10040.
Definition HA_PH_ENT  : Z := 56.
Definition HA_PH_NUM  : Z := 11.

Lemma ha_entry_eq : Z.of_N Asan.M.init_pc = HA_ENTRY.
Proof. reflexivity. Qed.
Lemma ha_phdrs_eq : HAPH = {| ph_addr := 0x10040%N; ph_ent := 56%N; ph_num := 11%N |}.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition HAITAB : itab := mk_itab HASEGS HA_TEXT_LO HA_TEXT_N.

Lemma ha_IT_ok : itab_sound HASEGS HAITAB.
Proof. apply mk_itab_sound. Qed.

(* [comment removed for export] *)
Lemma ha_segs_eq : HASEGS = [Asan_segment_000; Asan_segment_001;
                            Asan_segment_002; Asan_segment_003].
Proof. reflexivity. Qed.

Lemma ha_wx : wx_segs_nowrap HASEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma find_segment1_none_outside : forall segs lo hi x,
  segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma ha_segs_in_hull : segs_in_hull_b HASEGS HA_IMG_LO HA_IMG_HI = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ha_outside_hull : forall x, (x < HA_IMG_LO \/ HA_IMG_HI <= x) -> find_segment HASEGS x 1 = None.
Proof. intros x Hx. exact (find_segment1_none_outside HASEGS HA_IMG_LO HA_IMG_HI x ha_segs_in_hull Hx). Qed.

(* [comment removed for export] *)
Lemma ha_res_eq : segments_reserved HASEGS
  = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x18a000); (Z_to_bv 64 0x19a000, Z_to_bv 64 0x396000);
     (Z_to_bv 64 0x530000, Z_to_bv 64 0x79000); (Z_to_bv 64 0x5a9000, Z_to_bv 64 0x61f000)].
Proof. vm_compute. reflexivity. Qed.

Lemma ha_res_len : length (segments_reserved HASEGS) = 4%nat.
Proof. rewrite ha_res_eq. reflexivity. Qed.

Lemma ha_res_hull : Forall (fun iv => HA_IMG_LO <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= HA_IMG_HI)
                           (segments_reserved HASEGS).
Proof.
  rewrite ha_res_eq. unfold HA_IMG_LO, HA_IMG_HI.
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma ha_res_sizes : fold_right (fun iv acc => bv_unsigned (snd iv) + acc) 0 (segments_reserved HASEGS) = 0xbb8000.
Proof. rewrite ha_res_eq. cbn [fold_right snd]. rewrite ?u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ha_hex2 : scanN Asan_seg_bytes_002 64 0 495616 = true.
Proof. ltac2:(cert_refl_vm constr:(true)). Qed.
(* [comment removed for export] *)
Lemma ha_hex3 : scanN Asan_seg_bytes_003 64 0 6418432 = true.
Proof. ltac2:(cert_refl_vm constr:(true)). Qed.
Lemma ha_len2 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_002) / 2) = 495616%N.
Proof. vm_compute. reflexivity. Qed.
Lemma ha_len3 : Z.to_N (Uint63.to_Z (PrimString.length Asan_seg_bytes_003) / 2) = 6418432%N.
Proof. vm_compute. reflexivity. Qed.

Lemma ha_rw_window : forall m (x : word),
  HA_RW_LO <= bv_unsigned x < HA_RW_HI -> wview HASEGS m x <> None.
Proof.
  unfold HA_RW_LO, HA_RW_HI. intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment HASEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite ha_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 495616); [exact ha_hex2 | rewrite ha_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 6418432); [exact ha_hex3 | rewrite ha_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x5a9000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_002);
        [rewrite ha_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
        [rewrite ha_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma ha_ro_below_rw : forall seg, In seg HASEGS -> seg_writable seg = true -> HA_RW_LO <= Z.of_N (seg_base seg).
Proof.
  intros seg Hin Hw. rewrite ha_segs_eq in Hin. unfold HA_RW_LO.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hw |- *; try discriminate; lia.
Qed.
