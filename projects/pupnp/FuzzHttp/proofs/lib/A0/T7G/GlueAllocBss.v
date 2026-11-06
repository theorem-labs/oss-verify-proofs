(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes Image.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct AsanPlanImages AsanHexScan A0Img.
Import ListNotations.

Definition byte_z (s : PrimString.string) (off : N) : bool :=
  match hex_byte_at s off with Some b => Z.eqb (bv_unsigned b) 0 | None => false end.
Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then byte_z s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.
Lemma zscanN_sound : forall s fuel base n,
  zscanN s fuel base n = true -> forall i, (i < n)%N -> hex_byte_at s (base + i)%N = Some (Z_to_bv 8 0).
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + assert (i = 0%N) by lia. subst i. rewrite N.add_0_r. unfold byte_z in H.
      destruct (hex_byte_at s base) as [b|]; [| discriminate]. apply Z.eqb_eq in H. f_equal. apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2]. rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

Lemma depot_tab_zscan : zscanN Asan_seg_bytes_003 64 960472 4194304 = true.
Proof. apply (@bool_decide_eq_true_1 _ _); vm_cast_no_check (@eq_refl bool true). Qed.

Open Scope Z_scope.
Lemma depot_tab_rom : forall x, 1660888 <= x < 5855192 -> seg_rom asegs (wa x) = Some (Z_to_bv 8 0).
Proof.
  intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1. change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes].
  rewrite wa_unsigned by lia.
  destruct (find_segment asegs x 1) as [seg|] eqn:Hf.
  - apply find_segment_some_spec in Hf as (Hin & Hb & Ht).
    change asegs with ASEGS in Hin. rewrite asan_segs_eq in Hin.
    destruct Hin as [<-|[<-|[<-|[<-|[]]]]];
      cbn [seg_base seg_size seg_readable seg_perms seg_bytes string_has Ascii.eqb
           Asan_segment_000 Asan_segment_001
           Asan_segment_002 Asan_segment_003] in Hb, Ht |- *.
    + exfalso. cbn in Hb, Ht. lia.
    + exfalso. cbn in Hb, Ht. lia.
    + exfalso. cbn in Hb, Ht. lia.
    + cbn -[segment_byte_at]. cbn [segment_byte_at]. rewrite asan_len3.
      replace (Z.to_N (x - 700416) <? 5627904)%N with true by (symmetry; apply N.ltb_lt; lia).
      pose proof (zscanN_sound _ 64 960472 4194304 depot_tab_zscan (Z.to_N (x - 1660888)) ltac:(lia)) as ZS.
      replace (960472 + Z.to_N (x - 1660888))%N with (Z.to_N (x - 700416)) in ZS by lia. rewrite ZS. reflexivity.
  - exfalso. apply (find_segment_none_spec _ _ _ Hf Asan_segment_003);
      [change asegs with ASEGS; rewrite asan_segs_eq; cbn; tauto | cbn; lia].
Qed.
