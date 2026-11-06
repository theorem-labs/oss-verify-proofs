(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "bool"; "option"; "true"; "Some"; "false"; "nat"; "@Corelib.Numbers.BinNums"; "N"; "Z"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.MallocB.InvInitZ"; "zscanN"; "@Stdlib.ZArith.BinInt.Z"; "le"; "sub"; "to_N"; "add"; "of_N"; "eqb"; "lt"; "@stdpp.bitvector.definitions"; "Z_to_bv"; "bv"; "bv_unsigned"; "@LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics"; "hex_byte_at"; "@OSSVerify.tinyobjloader.fuzz_tobj_c.images.AsanUbsan"; "AsanUbsan_seg_bytes_003"; "@Corelib.Strings.PrimString"; "string"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B.ImageFacts"; "segsA"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3.SymState"; "image_byte"; "@Stdlib.NArith.BinNat.N"; "add"; "lt"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith NArith List Bool PArith Lia.
From Stdlib Require Import Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.tinyobjloader.fuzz_tobj_c.images Require Import AsanUbsan.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.B Require Import ImageFacts.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Definition zbyte_ok (s : PrimString.string) (off : N) : bool := ltac2:(tb__ "0|2|
S3S13Q8M0A1M1A1S2Lx;S15Vs;Voff;A2G1S10S14G0R1A2Z0A2Lb;S6X3x2").

Fixpoint zscanN (s : PrimString.string) (fuel : nat) (base n : N) : bool :=
  match fuel with
  | O => N.eqb n 0
  | S f =>
      if N.eqb n 0 then true
      else if N.eqb n 1 then zbyte_ok s base
      else let h := N.div2 n in (zscanN s f base h && zscanN s f (base + h) (n - h))%bool
  end.

Lemma zscanN_sound : ltac2:(tb__ "0|2|
S17S7S8S8S0S2SaR4R3R2R1A4S4A3S8S1bR1R3A2S0S3S13Q8M0A1M1A1S15R7S1aR5R2A2A2S5G1S12G0Z0A2A2A3F_;Fi;F_;Fn;Fbase;Ffuel;Fs;").
Proof.
  intros s fuel. induction fuel as [|f IH]; intros base n H i Hi; cbn [zscanN] in H.
  - apply N.eqb_eq in H. lia.
  - destruct (N.eqb_spec n 0) as [E0|Hn0]; [lia|].
    destruct (N.eqb_spec n 1) as [E1|Hn1].
    + subst n. replace i with 0%N by lia. rewrite N.add_0_r. unfold zbyte_ok in H.
      destruct (hex_byte_at s base) as [b|]; [|discriminate]. apply Z.eqb_eq in H. f_equal.
      apply bv_eq. rewrite H. reflexivity.
    + apply andb_prop in H as [H1 H2].
      rewrite N.div2_div in *.
      set (h := (n / 2)%N) in *.
      destruct (N.lt_ge_cases i h) as [Hl|Hge].
      * exact (IH _ _ H1 i Hl).
      * specialize (IH _ _ H2 (i - h)%N ltac:(lia)).
        replace (base + h + (i - h))%N with (base + i)%N in IH by lia. exact IH.
Qed.

Theorem image_zero_3 : ltac2:(tb__ "0|3|
S9S8S0S2SaS16U40SdScR2Ze6000M0A2A1R1A4S4A3SbG0R3A2SbSeR4SfR3A1A2Z643000A2S9S1SbR6R1A2S11R1SeR6SfR5A1A2A2A2S0S3S13Q8M1A1M2A1S19S18S12Q40R2A2A2S5G2S12G1Z0A2A2A3F_;Fx;F_;F_;F_;Fn;Flo;").
Proof.
  intros lo n Hs Hlo Hhi x Hx.
  pose proof (find_segment_A_rw x ltac:(lia)) as Hf.
  replace (x <? 0xe6000) with false in Hf by (symmetry; apply Z.ltb_ge; lia).
  destruct seg3_facts as (R3 & W3 & B3 & S3).
  assert (Hu : bv_unsigned (Z_to_bv 64 x) = x).
  { rewrite Z_to_bv_unsigned. apply (bv_wrap_small 64 x). change (bv_modulus 64) with (2 ^ 64). lia. }
  pose proof (zscanN_sound _ _ _ _ Hs (Z.to_N (x - lo)) ltac:(lia)) as Hb.
  replace (Z.to_N (lo - 0xe6000) + Z.to_N (x - lo))%N with (Z.to_N (x - 0xe6000)) in Hb by lia.
  unfold image_byte, memory_read. rewrite Hu. change (Z.of_N 1) with 1. rewrite Hf, R3, B3, S3.
  change (N.to_nat 1) with 1%nat. cbn [segment_read_bytes segment_byte_at].
  replace (Z.to_N (x - 942080) <? Z.to_N (Uint63.to_Z (PrimString.length AsanUbsan_seg_bytes_003) / 2))%N with true.
  2: { symmetry. apply N.ltb_lt. rewrite len_003. lia. }
  change 942080 with 0xe6000. rewrite Hb. reflexivity.
Qed.

Lemma zscan_IA : ltac2:(tb__ "0|1|
S0S2SaS16U40SdScZef2c0M0Ze6000A2A1SdScZ1702f0G0A2A1A4S4A3").
Proof. vm_cast_no_check (@eq_refl bool true). Qed.
