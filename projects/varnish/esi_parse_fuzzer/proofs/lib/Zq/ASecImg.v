(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.varnish.esi_parse_fuzzer.images Require Import AsanUbsan.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import MState Mem Cells Step Arr Bytes.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Import Asanhz7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yb Require Asan672.
From Stdlib Require Uint63.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AIface ACells.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Lemma asec_hex2 : scanN AsanUbsan_seg_bytes_002 64 0 8192 = true.
Proof. vm_compute. reflexivity. Qed.
Lemma asec_hex3 : scanN AsanUbsan_seg_bytes_003 64 0 5636096 = true.
Proof. (* [comment removed for export] *)
  apply (Asan672.scanN_prefix_zwin AsanUbsan_seg_bytes_003 32768 5636096 (Uint63.of_Z 65536) (Uint63.of_Z 11206656)).
  - vm_cast_no_check (eq_refl true).
  - vm_cast_no_check (eq_refl true).
  - reflexivity.
  - reflexivity.
  - vm_compute. discriminate.
  - vm_compute. discriminate.
Qed.
Lemma asec_len2 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_002) / 2) = 8192%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asec_len3 : Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2) = 5636096%N.
Proof. vm_compute. reflexivity. Qed.
Lemma asec_segs_eq : rsegs = [AsanUbsan_segment_000; AsanUbsan_segment_001;
                              AsanUbsan_segment_002; AsanUbsan_segment_003].
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma find_segment_some_spec : forall l addr n seg,
  find_segment l addr n = Some seg ->
  In seg l /\ (Z.of_N (seg_base seg) <= addr)%Z
  /\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z.
Proof.
  induction l as [|s l IH]; intros addr n seg Hf; [discriminate|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E.
  - injection Hf as ->. apply andb_true_iff in E as [E1 E2].
    apply Z.leb_le in E1. apply Z.leb_le in E2.
    split; [left; reflexivity | split; assumption].
  - destruct (IH addr n seg Hf) as (Hin & H1 & H2).
    split; [right; exact Hin | split; assumption].
Qed.
Lemma find_segment_none_spec : forall l addr n,
  find_segment l addr n = None ->
  forall seg, In seg l ->
    ~ ((Z.of_N (seg_base seg) <= addr)%Z
       /\ (addr + n <= Z.of_N (seg_base seg) + Z.of_N (seg_size seg))%Z).
Proof.
  induction l as [|s l IH]; intros addr n Hf seg Hin; [destruct Hin|].
  cbn [find_segment] in Hf.
  destruct (Z.leb (Z.of_N (seg_base s)) addr && Z.leb (addr + n) (Z.of_N (seg_base s) + Z.of_N (seg_size s)))%Z eqn:E;
    [discriminate|].
  destruct Hin as [<- | Hin].
  - intros [H1 H2]. apply andb_false_iff in E as [E | E].
    + apply Z.leb_gt in E. lia.
    + apply Z.leb_gt in E. lia.
  - exact (IH addr n Hf seg Hin).
Qed.

(* [comment removed for export] *)
Lemma seg_rom_data_some : forall x : word, 0xa8000 <= bv_unsigned x < 0x60a000 -> seg_rom rsegs x <> None.
Proof.
  intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1. change (N.to_nat 1) with 1%nat.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht). rewrite asec_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_readable seg_writable seg_perms seg_bytes string_has Ascii.eqb
           AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + cbn -[segment_byte_at].
      pose proof (segment_byte_at_some1 AsanUbsan_seg_bytes_002 8192 (Z.to_N (bv_unsigned x - 688128))
                    asec_hex2 ltac:(rewrite asec_len2; lia) ltac:(rewrite Z2N.id by lia; cbn in Hb, Ht; lia)) as S.
      destruct (segment_byte_at _ _); [discriminate| exfalso; exact (S eq_refl)].
    + cbn -[segment_byte_at].
      pose proof (segment_byte_at_some1 AsanUbsan_seg_bytes_003 5636096 (Z.to_N (bv_unsigned x - 696320))
                    asec_hex3 ltac:(rewrite asec_len3; lia) ltac:(rewrite Z2N.id by lia; cbn in Hb, Ht; lia)) as S.
      destruct (segment_byte_at _ _); [discriminate| exfalso; exact (S eq_refl)].
  - exfalso. destruct (Z.lt_ge_cases (bv_unsigned x) 0xaa000) as [Hl|Hl].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_002); [rewrite asec_segs_eq; cbn; tauto | cbn; lia].
    + apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003); [rewrite asec_segs_eq; cbn; tauto | cbn; lia].
Qed.

Lemma img_mrd_some : forall (m : mem) (x : word), 0xa8000 <= bv_unsigned x < 0x60a000 -> mrd rsegs m x <> None.
Proof. intros m x Hx. unfold mrd. destruct (m x); [discriminate| apply seg_rom_data_some; exact Hx]. Qed.

(* [comment removed for export] *)
Lemma img_junk : forall (m : mem) a n, 0xa8000 <= a -> a + n <= 0x60a000 -> 0 <= n -> junk_at rsegs m a n.
Proof.
  intros m a n H1 H2 Hn.
  exists (map (fun i => match mrd rsegs m (wz (a + Z.of_nat i)) with Some b => b | None => Z_to_bv 8 0 end) (seq 0 (Z.to_nat n))).
  rewrite length_map, length_seq. split; [lia|]. split; [lia|]. split; [rewrite length_map, length_seq; lia|].
  intros i Hi. rewrite length_map, length_seq in Hi.
  rewrite nth_error_map, nth_error_seq. destruct (Nat.ltb_spec i (Z.to_nat n)); [|lia]. cbn [option_map Nat.add].
  unfold wa. destruct (mrd rsegs m (wz (a + Z.of_nat i))) eqn:E; [reflexivity|]. exfalso.
  apply (img_mrd_some m (wz (a + Z.of_nat i))); [rewrite unsigned_lit by lia; lia| exact E].
Qed.
