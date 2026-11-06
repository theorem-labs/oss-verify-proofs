(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.openssl.punycode.images Require Import AsanUbsan.
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec StoreOk AgentLib AsanAcct AxSymExec3 AsanHexScan AsanHexZero CertRefl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Set Default Proof Mode "Classic".
Import ListNotations.
Import AX2.
Open Scope Z_scope.

Definition B_SEGS : list Segment := AsanUbsan.M.loaded_segments.
Definition B_PH : PhdrInfo := AsanUbsan.M.phdrs.

(* [comment removed for export] *)
Definition B_ENTRY   : Z := 0x194984.
Definition B_IMG_LO  : Z := 0x10000.
Definition B_IMG_HI  : Z := 0xbfd000.     (* [comment removed for export] *)
Definition B_TEXT_LO : Z := 0x194000.
Definition B_TEXT_HI : Z := 0x56b000.
Definition B_TEXT_N  : nat := 1006592.     (* [comment removed for export] *)
Definition B_RW_LO   : Z := 0x56b000.     (* [comment removed for export] *)
Definition B_RW_HI   : Z := 0xbfd000.
Definition B_PH_ADDR : Z := 0x10040.
Definition B_PH_ENT  : Z := 56.
Definition B_PH_NUM  : Z := 11.

Lemma B_entry_eq : Z.of_N AsanUbsan.M.init_pc = B_ENTRY.
Proof. reflexivity. Qed.
Lemma B_phdrs_eq : B_PH = {| ph_addr := 0x10040%N; ph_ent := 56%N; ph_num := 11%N |}.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition B_ITAB : itab := mk_itab B_SEGS B_TEXT_LO B_TEXT_N.

Lemma B_IT_ok : itab_sound B_SEGS B_ITAB.
Proof. apply mk_itab_sound. Qed.

(* [comment removed for export] *)
Lemma B_segs_eq : B_SEGS = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                            AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

Lemma B_wx : wx_segs_nowrap B_SEGS.
Proof. apply wx_segs_nowrap_of_b. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Definition B_segs_in_hull_b (segs : list Segment) (lo hi : Z) : bool :=
  forallb (fun seg => (lo <=? Z.of_N (seg_base seg)) && (Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <=? hi))%bool segs.

Lemma B_find_segment1_none_outside : forall segs lo hi x,
  B_segs_in_hull_b segs lo hi = true -> (x < lo \/ hi <= x) -> find_segment segs x 1 = None.
Proof.
  induction segs as [|s l IH]; intros lo hi x Hb Hx; [reflexivity|].
  cbn [B_segs_in_hull_b forallb] in Hb. apply andb_true_iff in Hb as [Hs Hl].
  apply andb_true_iff in Hs as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  cbn [find_segment].
  replace (Z.leb (Z.of_N (seg_base s)) x && Z.leb (x + 1) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%bool with false.
  - exact (IH lo hi x Hl Hx).
  - symmetry. apply andb_false_iff. destruct Hx as [Hx|Hx]; [left | right]; apply Z.leb_gt; lia.
Qed.

Lemma B_segs_in_hull : B_segs_in_hull_b B_SEGS B_IMG_LO B_IMG_HI = true.
Proof. vm_compute. reflexivity. Qed.

Lemma B_outside_hull : forall x, (x < B_IMG_LO \/ B_IMG_HI <= x) -> find_segment B_SEGS x 1 = None.
Proof. intros x Hx. exact (B_find_segment1_none_outside B_SEGS B_IMG_LO B_IMG_HI x B_segs_in_hull Hx). Qed.

(* [comment removed for export] *)
Lemma B_res_eq : segments_reserved B_SEGS
  = [(Z_to_bv 64 0x10000, Z_to_bv 64 0x184000); (Z_to_bv 64 0x194000, Z_to_bv 64 0x3d7000); (Z_to_bv 64 0x56b000, Z_to_bv 64 0x78000); (Z_to_bv 64 0x5e3000, Z_to_bv 64 0x61a000)].
Proof. vm_compute. reflexivity. Qed.

Lemma B_res_len : length (segments_reserved B_SEGS) = 4%nat.
Proof. rewrite B_res_eq. reflexivity. Qed.

Lemma B_res_hull : Forall (fun iv => B_IMG_LO <= bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= B_IMG_HI)
                           (segments_reserved B_SEGS).
Proof.
  rewrite B_res_eq. unfold B_IMG_LO, B_IMG_HI.
  repeat constructor; cbn [fst snd]; rewrite ?u64_lit by lia; lia.
Qed.

(* [comment removed for export] *)
Lemma B_res_sizes : fold_right (fun iv acc => bv_unsigned (snd iv) + acc) 0 (segments_reserved B_SEGS) = 0xbed000.
Proof. rewrite B_res_eq. cbn [fold_right snd]. rewrite ?u64_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma B_hex2 : scanN AsanUbsan_seg_bytes_002 64 0 491520 = true.
Proof. ltac2:(cert_refl_vm constr:(true)). Qed.
Lemma B_hex3 : scanN AsanUbsan_seg_bytes_003 64 0 6397952 = true.
Proof. (* [comment removed for export] *)
  apply (scanN_prefix_zwin AsanUbsan_seg_bytes_003 782336 6397952 (Uint63.of_Z 1564672) (Uint63.of_Z 11231232)).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.
Lemma B_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 491520%N.
Proof. vm_compute. reflexivity. Qed.
Lemma B_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 6397952%N.
Proof. vm_compute. reflexivity. Qed.

Lemma B_rw_window : forall m (x : word),
  B_RW_LO <= bv_unsigned x < B_RW_HI -> wview B_SEGS m x <> None.
Proof.
  unfold B_RW_LO, B_RW_HI. intros m x Hx. unfold wview. destruct (m x); [discriminate|].
  destruct (find_segment B_SEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    rewrite B_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_writable seg_perms seg_bytes string_has Ascii.eqb
           AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 491520); [exact B_hex2 | rewrite B_len2; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
    + cbn -[segment_byte_at]. apply (segment_byte_at_some1 _ 6397952); [exact B_hex3 | rewrite B_len3; lia | rewrite Z2N.id by lia; cbn in Hb, Ht; lia].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0x5e3000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002);
        [rewrite B_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003);
        [rewrite B_segs_eq; cbn; tauto | cbn; lia].
Qed.

(* [comment removed for export] *)
Lemma B_ro_below_rw : forall seg, In seg B_SEGS -> seg_writable seg = true -> B_RW_LO <= Z.of_N (seg_base seg).
Proof.
  intros seg Hin Hw. rewrite B_segs_eq in Hin. unfold B_RW_LO.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn in Hw |- *; try discriminate; lia.
Qed.
