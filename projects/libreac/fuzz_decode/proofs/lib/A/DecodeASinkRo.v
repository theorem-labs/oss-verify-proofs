(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: row D-A-sink-ro of fuzz_decode's composition step 5b: four Section hypotheses of
   lib/A/DecodeClose.v (a working branch 45061c42804), each in DecodeClose's text, at image
   A's instance of the Section variables: segs = decodesegs0, B = GrantB (lib/A/AD2l.v, the record the composition
   binds), KS = lib/A/AE2k.v:44 tfib_K, ameta_inv = Reusable/YE01.v:142 ameta_inv, asink_img_laws = Reusable/YE01.v:29
   asink_img_laws at SK = dec_A_sink_head, ro_below_ofl = lib/A/Prog/PaBase.v:23 ro_below_ofl at SK = dec_A_sink_head
   (the Theorem Labs lane forms lib/A/Prog/LLVMFuzzerTestOneInput_cg.v:175-181 names). The sink names are the ones lib/A/ACfn.v
   fixes for the driver (asink_none :46 / :59, ameta_inv :49 / :60).
   proves no function (kind: image facts): HB_META_KEPT and HB_SINK_IMG_LAWS are exact applications of the core's
   YE01.v:156 ameta_inv_kept and lib/A/AD1u.v:44 tfib_AIL at GrantB; HB_RO_BELOW_OFL and HB_ROM_NO_ERRNO are
   vm_compute checks over the image's loaded segments.
   dec_HB_SINK_KEPT is HB_SINK_KEPT in its AMENDED text: the HSINK_KEPT premise of the statement
   on a working branch at cb3945d8e0b (lib/A/Prog/LLVMFuzzerTestOneInput_cg.v:231-234), which
   adds `~ YI16.sink_open_fp FP` right after the journal premise, the premise YE01.v:85 asink_none_kept takes (:87).
   The text before the amendment (DecodeClose.v:334-337 on -close 45061c42804) is false: lib/A/DecodeASinkRoProbe.v
   HB_SINK_KEPT_false. *)
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import
YK11 YM05 YK04 YA0i YA0n YG00 YG01 YG0f YG0n YG0d YG0q YCbq.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require YI16 YE00 YE01.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require Import DecodeTFIB DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A Require AE2k AF0m AD2l AD1u.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog Require PaBase check_round_trip_cg.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
#[local] Existing Instance YK11.fx0.

Module YI16 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YI16.
Module YE00 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YE00.
Module YE01 := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YE01.
Module AE2k := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AE2k.
Module AF0m := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AF0m.
Module AD2l := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AD2l.
Module AD1u := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.AD1u.
Module PaBase := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.PaBase.
Module PC := OSSVerify.Proofs.libreac.fuzz_decode.lib.A.Prog.check_round_trip_cg.

(* DecodeClose.v:133 ro_below_ofl at the image's own sink head (PaBase.v:23 is cgif's lib/YC20.v:49 class). *)
Definition dec_A_ro_below_ofl (segs : list Segment) (rlo rhi : Z) : Prop :=
  @PaBase.ro_below_ofl segs rlo rhi dec_A_sink_head.

(* Image A's instance of DecodeClose.v's Section variables. *)
Local Abbreviation segs := decodesegs0.
Local Abbreviation B := AD2l.GrantB.
Local Abbreviation KS := AE2k.tfib_K.
Local Abbreviation asink_none := YE00.asink_none.
Local Abbreviation ameta_inv := YE01.ameta_inv.
Local Abbreviation asink_img_laws := (@YE01.asink_img_laws dec_A_sink_head).
Local Abbreviation ro_below_ofl := dec_A_ro_below_ofl.

(* ---- HB_SINK_IMG_LAWS (DecodeClose.v:358) ---------------------------------------------------------------------- *)
(* The core's sink record laws at GrantB: lib/A/AD1u.v:44 tfib_AIL is stated at tfibsegs (lib/A/AB1v.v:13) and the
   instance tfib_sink_head (lib/A/AE2k.v:36, ofl head A_ofl_head); both are by definition decodesegs0 and
   dec_A_sink_head (DecodeTFIB.v:19 and AB1v.v:13 are Asan.M.loaded_segments; AE2k.v:27 A_ofl_head and
   DecodeCalloc.v:97 DEC_A_ofl_head are the same symbol, musl's ofl_head). *)
Lemma dec_HB_SINK_IMG_LAWS : asink_img_laws segs B KS.
Proof. apply AD1u.tfib_AIL; first [exact AD2l.GrantB_syms | apply AR_laws_ok]. Qed.

(* ---- HB_META_KEPT (DecodeClose.v:338-341) ---------------------------------------------------------------------- *)
(* Reusable/YE01.v:156 ameta_inv_kept, from the record laws above; it takes no footprint premise. *)
Lemma dec_HB_META_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M,
    @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ameta_inv segs KS ly (mrestrict (w_H W0) mem0) M -> ameta_inv segs KS ly' (mrestrict (w_H W') mem') M.
Proof.
intros rc STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M HJ HM.
exact (YE01.ameta_inv_kept (rc := rc) (SK := dec_A_sink_head) segs B KS dec_HB_SINK_IMG_LAWS
  STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k M HJ HM).
Qed.

(* ---- HB_SINK_KEPT, amended (a Theorem Labs lane cb3945d8e0b, LLVMFuzzerTestOneInput_cg.v:231-234) ------------------------- *)
(* The amended premise at the instance (cg.v:188 rd W mem = mrestrict (w_H W) mem). Reusable/YE01.v:85
   asink_none_kept. *)
Lemma dec_HB_SINK_KEPT : forall (rc : YM05.RunCeil),
  forall STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k,
    @ajournal rc dec_A_sink_head segs B STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k ->
    ~ YI16.sink_open_fp FP ->
    asink_none segs KS (mrestrict (w_H W0) mem0) md0 -> asink_none segs KS (mrestrict (w_H W') mem') md'.
Proof.
intros rc STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ Hc HS.
exact (YE01.asink_none_kept (rc := rc) (SK := dec_A_sink_head) segs B KS dec_HB_SINK_IMG_LAWS
  STK sp0 FP ly S W0 mem0 md0 own ly' S' W' mem' md' k HJ Hc HS).
Qed.

(* ---- HB_RO_BELOW_OFL (DecodeClose.v:360) ----------------------------------------------------------------------- *)
(* Every non-writable loaded segment of the image ends at or below the sink's ofl head (one vm_compute check, as
   fuzz_grant's GrantClose.v grant_ro_segs_chk); the range [RLO, RHI) lies below it when RHI does. *)
Lemma dec_A_ro_segs_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? DEC_A_ofl_head))%bool
    segs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_HB_RO_BELOW_OFL : forall RLO RHI : Z, RHI <= DEC_A_ofl_head -> ro_below_ofl segs RLO RHI.
Proof.
intros RLO RHI HRHI. unfold dec_A_ro_below_ofl.
intros a [(s & Hin & Hw & Hr) | Hr]; cbn [YI16.sk_ofl_head dec_A_sink_head].
- pose proof (proj1 (forallb_forall _ _) dec_A_ro_segs_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
  cbn [orb] in Hb. apply Z.leb_le in Hb. lia.
- lia.
Qed.

(* ---- HB_ROM_NO_ERRNO (DecodeClose.v:330) ----------------------------------------------------------------------- *)
(* GrantB's errno word (lib/A/AD2l.v as_errno := AF0m.v:22 TFIB_ERRNO) lies outside every non-writable loaded
   segment of the image (one vm_compute check). *)
Lemma dec_A_rom_errno_chk :
  forallb (fun s : Segment => seg_writable s || (Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? AF0m.TFIB_ERRNO) ||
    (AF0m.TFIB_ERRNO + 4 <=? Z.of_N (seg_base s)))%bool segs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma dec_HB_ROM_NO_ERRNO : PC.dec_rom_no_errno B.
Proof.
intros a (s & Hin & Hw & Hr) He. cbn [as_errno AD2l.GrantB] in He.
pose proof (proj1 (forallb_forall _ _) dec_A_rom_errno_chk s Hin) as Hb. cbn beta in Hb. rewrite Hw in Hb.
cbn [orb] in Hb. apply Bool.orb_true_iff in Hb as [Hb | Hb]; apply Z.leb_le in Hb; lia.
Qed.

Print Assumptions dec_HB_SINK_IMG_LAWS.
Print Assumptions dec_HB_META_KEPT.
Print Assumptions dec_HB_SINK_KEPT.
Print Assumptions dec_HB_RO_BELOW_OFL.
Print Assumptions dec_HB_ROM_NO_ERRNO.
