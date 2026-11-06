(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/Reusable/YGcfCellsInit.v, with its module paths changed; 1 of its 37 lines of code is new or changed and 48 lines of the source are left out. *)
(* Theorem Labs, 2026-10-30: the image-free half of the start-up witness for the cf layer's two
   machine-cell fields exh_cell_cf and errb_cells_cf (YG0ncf.v) at init_state. Proves no function (start-up facts).
   Taken from the kit's earlier lib/Reusable/YGcfCellsInit.v, 2026-10-31: its Module CasanR2 (a
   copy of the cf layer's round-2 field text, made when preset's YG0ncf.v did not have the fields) and the two field-form
   theorems over that copy are REMOVED. The draft's YG0ncf.v now states the fields (exh_cell_cf, errb_cells_cf,
   errb_data_cf), and the step from the cells to the fields is the draft's YGcfInstBase.v exh_cell_cf_init /
   errb_cells_cf_init. This file keeps only the reduction to the cells:
   (1) exh_bytes_zero: the 31 exhausted bytes RegionInfo + 128 c + cf_exh_off (c = 1..31) read 0 when the first
       RegionInfo page reads 0 (range_zero at (ASp kRegionInfoOff, 4096)), given 0 <= cf_exh_off and
       cf_exh_off + 128 * 31 < 4096.
   (2) errb_words_zero: the five 8-byte words errb_cells_cf reads at init_state (cf_errbuf_obj + 0 / 16 / 32 / 40 / 48)
       read 0 when the 56-byte object reads 0 (range_zero at (ANum cf_errbuf_obj, 56)).
   (3) range_zero_ext: a range that reads 0 still reads 0 through any extension of the reader (rd_ext). This is how a
       start-up fact at the world W1 passes to every W' with wle W1 W'. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK04 YA0i YA0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0r.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05 YGcfNames.
Import ListNotations.
Local Open Scope Z_scope.

Lemma range_zero_ext : forall B ly (rd rd' : reader) r, rd_ext rd rd' -> range_zero B ly rd r -> range_zero B ly rd' r.
Proof. intros B ly rd rd' r X H i Hi. exact (X _ _ (H i Hi)). Qed.

Section I. Context {ci : CfImg}.
Variable B : asyms.
Variable ly : alayout.
Variable rd : reader.

(* the 31 exhausted bytes from the first RegionInfo page *)
Lemma exh_bytes_zero : 0 <= cf_exh_off -> cf_exh_off + 128 * 31 < 4096 ->
  range_zero B ly rd (ASp kRegionInfoOff, 4096) ->
  forall c, 1 <= c <= 31 -> cell_holds B ly rd (z1 (aoff (ASp (kRegionInfoOff + 128 * c)) cf_exh_off) 0).
Proof.
intros H0 H1 Z c Hc. unfold z1, c1.
apply (cell_zero_of_range B ly rd (ASp kRegionInfoOff) 4096 _ 1 Z); cbn [aoff aeval]; change (Z.of_nat 1) with 1; lia.
Qed.

(* any 8-byte word inside the 56-byte object *)
Lemma errb_obj_word_zero : range_zero B ly rd (ANum cf_errbuf_obj, 56) ->
  forall A, cf_errbuf_obj <= A -> A + 8 <= cf_errbuf_obj + 56 -> cell_holds B ly rd (z8 (ANum A) 0).
Proof.
intros Z A H1 H2. unfold z8, c8.
apply (cell_zero_of_range B ly rd (ANum cf_errbuf_obj) 56 _ 8 Z); cbn [aeval]; change (Z.of_nat 8) with 8; lia.
Qed.

(* the premises of the draft's YGcfInstBase.errb_cells_cf_init: the five words the field reads at init_state *)
Lemma errb_words_zero : range_zero B ly rd (ANum cf_errbuf_obj, 56) ->
  cell_holds B ly rd (z8 (ANum cf_errbuf_obj) 0) /\ cell_holds B ly rd (z8 (ANum (cf_errbuf_obj + 16)) 0) /\
  cell_holds B ly rd (z8 (ANum (cf_errbuf_obj + 32)) 0) /\ cell_holds B ly rd (z8 (ANum (cf_errbuf_obj + 40)) 0) /\
  cell_holds B ly rd (z8 (ANum (cf_errbuf_obj + 48)) 0).
Proof.
intros Z. pose proof (errb_obj_word_zero Z) as W.
split; [apply W; lia|]. split; [apply W; lia|]. split; [apply W; lia|]. split; apply W; lia.
Qed.
End I.
