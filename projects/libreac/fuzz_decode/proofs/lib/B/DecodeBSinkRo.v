(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: written for libreac/fuzz_decode's ASan+UBSan build (image B): the closing facts
   for five Section hypotheses of lib/B/DecodeBClose.v, each stated at the bindings the composition gives its Section
   variables:
     B := TfibB (lib/B/YD2l.v:12, TfibB_syms :68), KS := tfib_K (lib/B/YE2k.v), asink_syms / asink_none := a Theorem Labs lane's
     lib/Reusable/YE00.v, ameta_inv / asink_img_laws := lib/B/YE01.v at SK := dec_B_sink_head,
     ro_below_ofl := lib/A/Prog/PaBase.v:23 at SK := dec_B_sink_head, RLO / RHI := 0x98d88 / 0x99ff8 (the relro range
     of lib/B/YCeg.v in_ro_tfa), segs := decodesegsB0 (DecodeBClose.v:92).
   dec_HB_SINK_KEPT is HB_SINK_KEPT with the premise `~ YI16.sink_open_fp FP ->` after the journal premise (the amended
   form: HB_SINK_KEPT as typed is refuted by lib/B/DecodeBSinkRoProbe.v HB_SINK_KEPT_false); it and dec_HB_META_KEPT are
   a Theorem Labs lane's asink_none_kept / ameta_inv_kept (lib/B/YE01.v:85 / :156) over dec_HB_SINK_IMG_LAWS, which is the core's
   tfib_AIL (lib/B/YD1u.v:43) at TfibB. dec_HB_RO_BELOW_OFL and dec_HB_ROM_NO_ERRNO are computations over the image's
   loaded segments: every read-only segment ends at or below musl's ofl_head 0x5f49d0 and none meets errno's four bytes
   at TFIB_ERRNO 0x5d4234 (lib/B/YF0m.v), which lie in a writable segment. The A twin is lib/A/DecodeASinkRo.v. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YK04 YA0i YA0n YG00 YG0f YG0n YG0d YI16 YCbq YM05.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YE00.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require PaBase.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require YD2l YE2k YE01 YD1u YF0m.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require check_round_trip_cg.
Import ListNotations.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Module YE00 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YE00.
Module PaBase := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.PaBase.
Module BD2l := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YD2l.
Module BE2k := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YE2k.
Module BE01 := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YE01.
Module BD1u := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YD1u.
Module BF0m := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.YF0m.
Module PC := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.check_round_trip_cg.

Local Notation segs := decodesegsB0.

(* HB_SINK_IMG_LAWS (DecodeBClose.v:352): the core's tfib_AIL at TfibB. tfib_AIL is stated at tfibsegs and the core's
   sink head tfib_sink_head; both are image B's (AsanUbsan.M.loaded_segments, musl ofl_head 0x5f49d0). *)
Lemma dec_HB_SINK_IMG_LAWS : @BE01.asink_img_laws dec_B_sink_head segs BD2l.TfibB BE2k.tfib_K.
Proof. exact (BD1u.tfib_AIL BD2l.TfibB BD2l.TfibB_syms). Qed.

(* HB_SINK_KEPT (DecodeBClose.v:328-331), amended with `~ YI16.sink_open_fp FP ->` after the journal premise. *)
Lemma dec_HB_SINK_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
    @ajournal rc dec_B_sink_head segs BD2l.TfibB STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ~ YI16.sink_open_fp FP ->
    YE00.asink_none segs BE2k.tfib_K (mrestrict (w_H W0) mem0) md0 ->
    YE00.asink_none segs BE2k.tfib_K (mrestrict (w_H W') mem') md'.
Proof.
intros rc STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ Hcl Hn.
refine (BE01.asink_none_kept segs BD2l.TfibB BE2k.tfib_K dec_HB_SINK_IMG_LAWS
          STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k _ Hcl Hn).
exact HJ.
Qed.

(* HB_META_KEPT (DecodeBClose.v:332-335), as typed: ameta_inv reads memory only and ameta_inv_kept takes no
   footprint premise. *)
Lemma dec_HB_META_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
    @ajournal rc dec_B_sink_head segs BD2l.TfibB STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    BE01.ameta_inv segs BE2k.tfib_K ly (mrestrict (w_H W0) mem0) M ->
    BE01.ameta_inv segs BE2k.tfib_K ly' (mrestrict (w_H W') mem') M.
Proof.
intros rc STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M HJ HM.
refine (BE01.ameta_inv_kept segs BD2l.TfibB BE2k.tfib_K dec_HB_SINK_IMG_LAWS
          STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M _ HM).
exact HJ.
Qed.

(* HB_RO_BELOW_OFL (DecodeBClose.v:354), for every RLO / RHI with RHI at or below the sink head's ofl_head. *)
Lemma dec_ro_segs_below_ofl :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? DEC_B_ofl_head))%bool
    segs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_HB_RO_BELOW_OFL : forall RLO RHI : Z, RHI <= DEC_B_ofl_head ->
  @PaBase.ro_below_ofl segs RLO RHI dec_B_sink_head.
Proof.
intros RLO RHI Hhi a Hro. change (a < DEC_B_ofl_head).
destruct Hro as [(s & Hin & Hw & Hr) | Hg].
- pose proof (proj1 (forallb_forall _ _) dec_ro_segs_below_ofl s Hin) as Hb. cbv beta in Hb.
  rewrite Hw in Hb. cbn [orb] in Hb. apply Z.leb_le in Hb.
  exact (Z.lt_le_trans _ _ _ (proj2 Hr) Hb).
- exact (Z.lt_le_trans _ _ _ (proj2 Hg) Hhi).
Qed.

(* HB_ROM_NO_ERRNO (DecodeBClose.v:324): errno's four bytes meet no read-only segment. *)
Lemma dec_rom_segs_avoid_errno :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? BF0m.TFIB_ERRNO)
                              || (BF0m.TFIB_ERRNO + 4 <=? Z.of_N (seg_base s)))%bool
    segs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_HB_ROM_NO_ERRNO : PC.dec_rom_no_errno BD2l.TfibB.
Proof.
intros a (s & Hin & Hw & Hr) He. change (BF0m.TFIB_ERRNO <= a < BF0m.TFIB_ERRNO + 4) in He.
pose proof (proj1 (forallb_forall _ _) dec_rom_segs_avoid_errno s Hin) as Hb. cbv beta in Hb.
rewrite Hw in Hb. cbn [orb] in Hb. apply Bool.orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb.
- (* the segment ends at or below errno: a < its end <= errno <= a *)
  exact (Z.lt_irrefl a (Z.lt_le_trans _ _ _ (proj2 Hr) (Z.le_trans _ _ _ Hb (proj1 He)))).
- (* the segment starts at or above errno + 4: errno + 4 <= its start <= a < errno + 4 *)
  exact (Z.lt_irrefl _ (Z.le_lt_trans _ _ _ (Z.le_trans _ _ _ Hb (proj1 Hr)) (proj2 He))).
Qed.

(* One Check per hypothesis type, at the composition's bindings. *)
Check (dec_HB_SINK_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
    @ajournal rc dec_B_sink_head segs BD2l.TfibB STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ~ YI16.sink_open_fp FP ->
    YE00.asink_none segs BE2k.tfib_K (mrestrict (w_H W0) mem0) md0 ->
    YE00.asink_none segs BE2k.tfib_K (mrestrict (w_H W') mem') md').
Check (dec_HB_META_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
    @ajournal rc dec_B_sink_head segs BD2l.TfibB STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    BE01.ameta_inv segs BE2k.tfib_K ly (mrestrict (w_H W0) mem0) M ->
    BE01.ameta_inv segs BE2k.tfib_K ly' (mrestrict (w_H W') mem') M).
Check (dec_HB_SINK_IMG_LAWS : (fun s b k => @BE01.asink_img_laws dec_B_sink_head s b k) segs BD2l.TfibB BE2k.tfib_K).
Check (dec_HB_RO_BELOW_OFL 0x98d88 0x99ff8 ltac:(unfold DEC_B_ofl_head; apply Z.leb_le; reflexivity)
  : (fun s rlo rhi => @PaBase.ro_below_ofl s rlo rhi dec_B_sink_head) segs 0x98d88 0x99ff8).
Check (dec_HB_ROM_NO_ERRNO : PC.dec_rom_no_errno BD2l.TfibB).

Print Assumptions dec_HB_SINK_KEPT.
Print Assumptions dec_HB_META_KEPT.
Print Assumptions dec_HB_SINK_IMG_LAWS.
Print Assumptions dec_HB_RO_BELOW_OFL.
Print Assumptions dec_HB_ROM_NO_ERRNO.
