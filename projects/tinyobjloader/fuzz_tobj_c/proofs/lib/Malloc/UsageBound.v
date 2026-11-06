(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)


From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require TermBlob.
#[local] Ltac2 tbs__ () := ["@Corelib.Numbers.BinNums"; "Z"; "@Corelib.Init.Logic"; "eq"; "and"; "@Corelib.Init.Datatypes"; "length"; "list"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocInv"; "Inv"; "bounded"; "layout_ok"; "class_sum"; "keys"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocModel"; "sptr"; "region"; "st_areas"; "st_avail_meta_area_count"; "st_avail_meta_areas"; "st_meta_alloc_shift"; "st_regions"; "usage_of"; "@Stdlib.ZArith.BinInt.Z"; "le"; "lt"; "mul"; "of_nat"; "pow"; "@OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc.MallocLayout"; "ledger_ok"; "vm_ok"; "@Corelib.Init.Peano"; "le"].
#[local] Ltac2 tb__ s := OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib.TermBlob.dec2 (tbs__ ()) s.
From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib.Malloc Require Import
  MallocModel MallocInv MallocLayout MallocWfBound AllocMetaGrow.
From OSSVerify.Proofs.tinyobjloader.fuzz_tobj_c.lib Require LiaFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Lemma class_sum_leX X R U s sc : ltac2:(tb__ "0|1|
S5VX;VR;VU;Vs;A4S2S12Z0S8VX;Vs;Vsc;A3M0A2S12G0S14Z20S15S3SaS9Vs;A1A2A1A2A2A2F_;").
Proof.
  intros HI. unfold class_sum.
  assert (G : forall l, (forall g, In g l -> 0 <= contrib X s sc g <= 32) ->
            0 <= fold_right (fun g acc => contrib X s sc g + acc) 0 l <= 32 * Z.of_nat (length l)).
  { induction l as [|x t IH]; intros H; cbn [fold_right length]; [lia|].
    pose proof (H x (or_introl eq_refl)). assert (IH' := IH (fun g Hg => H g (or_intror Hg))). lia. }
  apply G. intros g _. unfold contrib. destruct (MTX X s g) as [[| |am]|] eqn:E; try lia.
  pose proof (inv_groups HI g am E) as ((M1 & _) & _). destruct (am_sc am =? sc); lia.
Qed.

Theorem usage_lt48 C X R U s L vm : ltac2:(tb__ "0|2|
S5VX;VR;VU;Vs;A4S7VL;Vs;A2S18VL;Vs;Vvm;A3S17VC;Vvm;A2S0S1S0VU;R1A1Z0M0A3Fc;S0S2S12G0S11Vs;R1A2M1A2S13G1S16Z2Z30A2A2A2Fsc;F_;F_;F_;F_;F_;").
Proof.
  intros HI HL HV HLG HU sc.
  pose proof (inv_ctx HI) as (C1 & C2 & C3 & C4 & C5 & Crest).
  pose proof (areas_bound X R U s L C vm HI HL HV HLG) as AB.
  pose proof (keys_le_areas s (inv_keys HI)) as KA.
  assert (K : forall c, 0 <= c < 48 -> 0 <= usage_of s c < 2 ^ 48).
  { intros c Hc. rewrite (inv_usage HI c Hc), (HU c). pose proof (class_sum_leX X R U s c HI). unfold METAS_PER_AREA in *. nia. }
  destruct (Z_lt_dec sc 0) as [Hneg|Hnneg].
  - replace (usage_of s sc) with (usage_of s 0) by (unfold usage_of, znth; replace (Z.to_nat sc) with (Z.to_nat 0) by lia; reflexivity). apply K. lia.
  - destruct (Z_lt_dec sc 48) as [Hlt|Hge]; [apply K; lia|].
    unfold usage_of, znth. rewrite nth_overflow; [lia|]. rewrite C2. lia.
Qed.

Theorem bounded_usage C X R U s s' L vm : ltac2:(tb__ "0|0|
S6Vs;A1S5VX;VR;VU;Vs';A4S7VL;Vs';A2S18VL;Vs';Vvm;A3S17VC;Vvm;A2S0S1S0VU;R1A1Z0A3Fc;S1S0SfVs';A1SfVs;A1A3S1S4SaA1ScVs';A1ScVs;A1A3S1S0SdVs';A1SdVs;A1A3S1SaSeVs';A1SeVs;A1A3S19S3SbS10Vs;A1A2S3SbS10Vs';A1A2A2S6Vs';A1F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;F_;").
Proof.
  intros (B1 & B2 & B3 & B4) HI HL HV HLG HU E1 E2 E3 E4 E5.
  split; [exact (usage_lt48 C X R U s' L vm HI HL HV HLG HU)|].
  rewrite E1, E2, E3, E4. split; [exact B2|]. split; [exact B3|].
  destruct B4 as [B4|B4]; [left; exact B4 | right; lia].
Qed.
