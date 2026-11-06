(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfAroBridge.v, with its module paths changed; 26 of its 46 lines of code are new or changed and 8 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30 (row A19 of omx-clap-core/fuzz_preset's cf instance; field round 3 part 3c re-fit
   2026-10-31).  The arodata bridge: preset's READER form of the read-only image bytes (lib/Spec/PresetRodata.v
   arodata_okP, over `aview segs (w_H W) mem`, the form preset's walks and journals carry) gives the cf layer's VALUE
   form YG0dcf.arodata_ok_cf (an overlay byte at a non-owned address of YG0dcf.aro_addr_cf equals the image's byte).
   Part 3c: aro_addr_cf covers the RELRO range [cf_relro_lo, cf_relro_hi) AND each range of cf_ro_reads (the
   class-full report's read-only reads).
   Why it holds: each covered address lies in a segment (the unit image row YG0ncf.relro_seg_t, both conjuncts), and
   the world's hidden set is never on a segment (YA0n.world's w_Hoff, YK04.H_off_segments), so there `aview` reads
   mem's byte when mem holds one; errno's four bytes are apart from every covered range (YG0ncf.errno_relro_t, both
   conjuncts), so the reader form's errno exclusion does not bite; the reader form then equates that byte with the
   image's (seg_rom).  The reader form covers RELRO and the NON-WRITABLE segments (PresetRodata.in_roP), so a
   cf_ro_reads range needs a non-writable segment that holds it ([RONW]); relro_seg_t's Forall gives only 'some
   segment'.  Every covered address must lie inside the 64-bit address space ([HTOP], [RONW]'s last conjunct), so that
   `bv_unsigned (Z_to_bv 64 a) = a` on it.
   IMAGE-FREE: no address, no image number; each unit discharges relro_seg_t / errno_relro_t / HTOP / RONW at its own
   image (preset: lib/A/CfAroPresetA.v, lib/AU/CfAroPresetB.v).
   rule 24: no function proved (kind: a generic bridge between two existing predicates). *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YP09 YK04 YA0n YG0f YG0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames YG0ncf YG0dcf.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require PresetRodata.
Local Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {ci : CfImg} {cp : CfParams}.

(* The image fact a cf_ro_reads range needs beyond relro_seg_t: a NON-WRITABLE segment holds it, inside 2^64. *)
Definition ro_reads_nw_t (segs : list Segment) : Prop :=
  Forall (fun r => fst r + snd r <= 2 ^ 64 /\ exists sg, In sg segs /\ seg_writable sg = false /\
    Z.of_N (seg_base sg) <= fst r /\ fst r + snd r <= Z.of_N (seg_base sg) + Z.of_N (seg_size sg)) cf_ro_reads.

(* One covered byte: an address of a segment, inside 2^64, off errno, where the reader form holds, reads as the
   image's byte from any overlay byte. *)
Lemma aro_byte : forall (segs : list Segment) (B : asyms) (W : world segs) (mem : word -> option byte) sg a b,
  In sg segs -> Z.of_N (seg_base sg) <= a < Z.of_N (seg_base sg) + Z.of_N (seg_size sg) -> a < 2 ^ 64 ->
  mem (Z_to_bv 64 a) = Some b ->
  aview segs (w_H W) mem a = option_map (fun b : byte => bv_unsigned b) (seg_rom segs (Z_to_bv 64 a)) ->
  seg_rom segs (Z_to_bv 64 a) = Some b.
Proof.
intros segs B W mem sg a b Hin Hs HT Hm HR.
assert (Ua : bv_unsigned (Z_to_bv 64 a) = a)
  by (apply Z_to_bv_small; change (bv_modulus 64) with (2 ^ 64); lia).
assert (HN : w_H W (Z_to_bv 64 a) = false).
{ destruct (w_H W (Z_to_bv 64 a)) eqn:E; [|reflexivity]. exfalso.
  pose proof (w_Hoff W _ E) as F. rewrite Ua in F.
  exact (find_segment_none_spec segs a 1 F sg Hin ltac:(split; lia)). }
unfold aview, mbyte, mrestrict in HR. rewrite HN, Hm in HR. cbn [option_map] in HR.
destruct (seg_rom segs (Z_to_bv 64 a)) as [b'|] eqn:Er; cbn [option_map] in HR; [|discriminate HR].
injection HR as HR. f_equal. apply bv_eq. symmetry. exact HR.
Qed.

(* The bridge.  [W] is any world over [segs]: only its w_Hoff field is read. *)
Theorem arodata_ok_cf_of_P : forall (segs : list Segment) (B : asyms) (W : world segs) (mem : word -> option byte),
  relro_seg_t segs -> errno_relro_t B -> cf_relro_hi <= 2 ^ 64 -> ro_reads_nw_t segs ->
  PresetRodata.arodata_okP segs cf_relro_lo cf_relro_hi B (aview segs (w_H W) mem) ->
  arodata_ok_cf segs B mem.
Proof.
intros segs B W mem ((sg & Hin & L & R) & _) (HE & HEr) HTOP RONW HP a b Hm Ha HO.
destruct Ha as [Ha | Ha].
- assert (NE : ~ (as_errno B <= a < as_errno B + 4)) by lia.
  exact (aro_byte segs B W mem sg a b Hin ltac:(lia) ltac:(lia) Hm (HP a (or_intror Ha) HO NE)).
- apply Exists_exists in Ha as (r & Hr & Hra). unfold in_zr in Hra.
  unfold ro_reads_nw_t in RONW. rewrite Forall_forall in RONW, HEr.
  destruct (RONW r Hr) as (T & sg' & Hin' & NW & L' & R').
  assert (NE : ~ (as_errno B <= a < as_errno B + 4)) by (pose proof (HEr r Hr); lia).
  assert (IN : PresetRodata.in_roP segs cf_relro_lo cf_relro_hi a)
    by (left; exists sg'; split; [exact Hin' | split; [exact NW | lia]]).
  exact (aro_byte segs B W mem sg' a b Hin' ltac:(lia) ltac:(lia) Hm (HP a IN HO NE)).
Qed.

End a.
