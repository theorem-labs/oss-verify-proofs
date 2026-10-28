(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import Ubsan.
From Ltac2 Require Import Ltac2.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanHexScan CertRefl.
Set Default Proof Mode "Classic".
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2.
Open Scope Z_scope.

Definition HSEGS : list Segment := Ubsan.M.loaded_segments.
Definition HPH : PhdrInfo := Ubsan.M.phdrs.

(* [comment removed for export] *)
Definition H0_ENTRY   : Z := 0xe1830.
Definition H0_IMG_LO  : Z := 0x10000.
Definition H0_IMG_HI  : Z := 0x354000.     (* [comment removed for export] *)
Definition H0_TEXT_LO : Z := 0xe1000.
Definition H0_TEXT_HI : Z := 0x2c1000.
Definition H0_TEXT_N  : nat := 491520.     (* [comment removed for export] *)
Definition H0_RW_LO   : Z := 0x2c1000.     (* [comment removed for export] *)
Definition H0_RW_HI   : Z := 0x354000.
Definition H0_PH_ADDR : Z := 0x10040.
Definition H0_PH_ENT  : Z := 56.
Definition H0_PH_NUM  : Z := 10.

Lemma h0_entry_eq : Z.of_N Ubsan.M.init_pc = H0_ENTRY.
Proof. reflexivity. Qed.
Lemma h0_phdrs_eq : HPH = {| ph_addr := 0x10040%N; ph_ent := 56%N; ph_num := 10%N |}.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition HITAB : itab := mk_itab HSEGS H0_TEXT_LO H0_TEXT_N.

Lemma h0_IT_ok : itab_sound HSEGS HITAB.
Proof. apply mk_itab_sound. Qed.

(* [comment removed for export] *)
Lemma h0_segs_eq : HSEGS = [Ubsan_segment_000; Ubsan_segment_001;
                            Ubsan_segment_002; Ubsan_segment_003].
Proof. reflexivity. Qed.

Lemma h0_wx : wx_segs_nowrap HSEGS.
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

Lemma h0_segs_in_hull : segs_in_hull_b HSEGS H0_IMG_LO H0_IMG_HI = true.
Proof. vm_compute. reflexivity. Qed.

Lemma h0_outside_hull : forall x, (x < H0_IMG_LO \/ H0_IMG_HI <= x) -> find_segment HSEGS x 1 = None.
Proof. intros x Hx. exact (find_segment1_none_outside HSEGS H0_IMG_LO H0_IMG_HI x h0_segs_in_hull Hx). Qed.

(* [comment removed for export] *)
Lemma h0_res_eq : segments_reserved HSEGS
  = [(Z_to_bv 64 0x10000, Z_to_bv 64 0xd1000); (Z_to_bv 64 0xe1000, Z_to_bv 64 0x1e0000);
     (Z_to_bv 64 0x2c1000, Z_to_bv 64 0x5d000); (Z_to_bv 64 0x31e000, Z_to_bv 64 0x36000)].
Proof. vm_compute. reflexivity. Qed.

Lemma h0_res_len : length (segments_reserved HSEGS) = 4%nat.
Proof. rewrite h0_res_eq. reflexivity. Qed.

Lemma h0_res_hull : Forall (fun iv => H0_IMG_LO <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= H0_IMG_HI)
                           (segments_reserved HSEGS).
Proof.
  rewrite h0_res_eq. unfold H0_IMG_LO, H0_IMG_HI.
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma h0_res_sizes : fold_right (fun iv acc => bv_unsigned (snd iv) + acc) 0 (segments_reserved HSEGS) = 0x344000.
Proof. rewrite h0_res_eq. cbn [fold_right snd]. rewrite ?u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma h0_hex2 : scanN Ubsan_seg_bytes_002 64 0 380928 = true.
Proof. ltac2:(cert_refl_vm constr:(true)). Qed.
(* [comment removed for export] *)
Lemma h0_hex3 : scanN Ubsan_seg_bytes_003 64 0 221184 = true.
Proof. ltac2:(cert_refl_vm constr:(true)). Qed.
Lemma h0_len2 : Z.to_N (Uint63.to_Z (PrimString.length Ubsan_seg_bytes_002) / 2) = 380928%N.
Proof. vm_compute. reflexivity. Qed.
Lemma h0_len3 : Z.to_N (Uint63.to_Z (PrimString.length Ubsan_seg_bytes_003) / 2) = 221184%N.
Proof. vm_compute. reflexivity. Qed.

Lemma h0_rw_window : forall m (x : word),
  H0_RW_LO <= bv_unsigned x < H0_RW_HI -> wview HSEGS m x <> None.
Proof.
  unfold H0_RW_LO, H0_RW_HI. intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment HSEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite h0_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           Ubsan_segment_000 Ubsan_segment_001
           Ubsan_segment_002 Ubsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 380928); [exact h0_hex2 | rewrite h0_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 221184); [exact h0_hex3 | rewrite h0_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x31e000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf Ubsan_segment_002);
        [rewrite h0_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf Ubsan_segment_003);
        [rewrite h0_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma h0_ro_below_rw : forall seg, In seg HSEGS -> seg_writable seg = true -> H0_RW_LO <= Z.of_N (seg_base seg).
Proof.
  intros seg Hin Hw. rewrite h0_segs_eq in Hin. unfold H0_RW_LO.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hw |- *; try discriminate; lia.
Qed.
