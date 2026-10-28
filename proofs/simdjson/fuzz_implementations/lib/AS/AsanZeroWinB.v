(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63.
From Corelib Require Import PrimString.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From OssFuzzTheorems.simdjson.fuzz_implementations.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.simdjson.fuzz_implementations.lib.AS Require Import PropExec AsanAcct AsanHexScan AsanHexZero AsanPlanImagesB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition ZWIN_LO : Z := 0x187000.
Definition ZWIN_HI : Z := 0x6e0000.

Lemma asan_zwin3 : zwin AsanUbsan_seg_bytes_003 (Uint63.of_Z 49152) (Uint63.of_Z 11214848) = true.
Proof. vm_cast_no_check (eq_refl true). Qed.

Lemma asan_zero_win : forall x : word, ZWIN_LO <= bv_unsigned x < ZWIN_HI -> seg_rom ASEGS x = Some (Z_to_bv 8 0).
Proof.
  intros x Hx. unfold ZWIN_LO, ZWIN_HI in Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1.
  destruct (find_segment ASEGS (bv_unsigned x) 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht). rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_readable seg_perms seg_bytes string_has Ascii.eqb
           AsanUbsan_segment_000 AsanUbsan_segment_001
           AsanUbsan_segment_002 AsanUbsan_segment_003] in Hb, Ht |- *.
    + exfalso. lia.
    + exfalso. lia.
    + exfalso. lia.
    + change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at].
      set (off := Z.to_N (bv_unsigned x - Z.of_N 1576960)).
      assert (Ho : (24576 <= off < 5632000)%N) by (unfold off; lia).
      replace (off <? Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2))%N with true
        by (symmetry; apply N.ltb_lt; rewrite asan_len3; lia).
      rewrite (zwin_hex_byte_at AsanUbsan_seg_bytes_003 (Uint63.of_Z 49152) (Uint63.of_Z 11214848) off asan_zwin3);
        [reflexivity | vm_compute; discriminate | change (Uint63.to_Z (Uint63.of_Z 49152)) with 49152; lia
        | change (Uint63.to_Z (Uint63.of_Z 49152)) with 49152; change (Uint63.to_Z (Uint63.of_Z 11214848)) with 11214848; lia].
  - exfalso. apply (find_segment_none_spec _ _ _ Hf AsanUbsan_segment_003); [rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.
