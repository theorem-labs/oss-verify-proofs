(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgParse.v of this library, for image B
   (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f). What differs:
   the image modules are image B's lib/AU twins, the segments are image B's (lib/AU/PPgParse0.v .. PPgParse4.v,
   PPgParse2L.v, over lib/AU/PPgParseCx.v), the entry is 0x80ba4 and reac_box_catalogue's entry 0x8107c, the
   strlen wrapper's text is lib/AU/Rt/StrlenDef.v's, and the instance is at image B's read-only window
   [0x97c20, 0x99e68) (lib/AU/PPgLib.v RO_LO / RO_HI: .data.rel.ro start .. .got end, section headers) and table
   PIN_CAT = 0x98000 (lib/AU/PPgSat.v). The theorem names and statements are the A file's at image B's numbers. *)
(* Modified by Theorem Labs, 2026-11: copied from proofs/reac-pw/fuzz_pin/lib/AU/PPgParse.v, with its module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the asan-ubsan twin of lib/A/PPgParse.v of this library, for image B
   (fuzz_pin.asan-ubsan, sha256 d6f83d30152279dadae39fc626707a0037090a8909a186dac3c362b12088201f). What differs:
   the image modules are image B's lib/AU twins, the segments are image B's (lib/AU/PPgParse0.v .. PPgParse4.v,
   PPgParse2L.v, over lib/AU/PPgParseCx.v), the entry is 0x80ba4 and reac_box_catalogue's entry 0x8107c, the
   strlen wrapper's text is lib/AU/Rt/StrlenDef.v's, and the instance is at image B's read-only window
   [0x97c20, 0x99e68) (lib/AU/PPgLib.v RO_LO / RO_HI: .data.rel.ro start .. .got end, section headers) and table
   PIN_CAT = 0x98000 (lib/AU/PPgSat.v). The theorem names and statements are the A file's at image B's numbers. *)
(* reac_box_pin_parse of reac-pw/fuzz_pin, image B (fuzz_pin.asan-ubsan, 0x80ba4): the contract tpin_parse_specX
   (lib/A/PPgCSpec.v) proved, by the walk's six segments composed:
     0x80ba4 -> 0x80cac (PPgParse0.v pp_seg0), 0x80cac -> 0x80cd0 | 0x80e98 (PPgParse1.v pp_seg1),
     0x80cd0 -> 0x80d40 (PPgParse2.v pp_seg2), the row loop 0x80d40 -> 0x80dd0 | 0x80e98 (PPgParse2L.v pp_seg2L),
     0x80dd0 -> 0x80e98 (PPgParse3.v pp_seg3), 0x80e98 -> `ret` (PPgParse4.v pp_seg4),
   over the context record, cut states and continuations of lib/AU/PPgParseCx.v. *)
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Reusable Require Import YK11 YP0m YP09 YI04 YG0v YG00 YG0f YG0n YG0d YCbq YC5d YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.Prog Require Import pin_spec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import AWalkFw0 YCeh.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.A Require Import PPgBase PPgWrap PPgCSpec.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgParseCx.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU.Rt Require Import StrlenDef.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require PPgParse0 PPgParse1 PPgParse2 PPgParse2L PPgParse3 PPgParse4.
From OSSVerify.Proofs.reac_pw.fuzz_pin.lib.AU Require Import PPgSat.
Import ListNotations.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Variable B : asyms.  Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.          Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.                Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes tfibsegs B 0.   Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.             Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis ASTRCSPN : astrcspn_realizes tfibsegs B 0x4191c.
Hypothesis ASTRLEN : astrlen_realizes tfibsegs B 0x41908.
Hypothesis ASTRNCMP : astrncmp_realizes tfibsegs B 0x41914.
Variables RLO RHI cat : Z.  Variables TP DP : nat -> Z.
Hypothesis CATALOGUE : tpin_catalogue_specX tfibsegs B MT 0x8107c cat.
(* pin's .data.rel.ro start .. .got end, and the table, lie in the image (discharged in the close) *)
Hypothesis RELRO : forall a, RLO <= a < RHI -> in_img tfibsegs a.
Hypothesis CATIMG : forall x, cat <= x < cat + CAT_BYTES -> in_img tfibsegs x.

Theorem pin_pb_parseX : tpin_parse_specX tfibsegs B MT RLO RHI 0x80ba4 cat 0x20d80 TP DP.
Proof.
assert (S4 : PP_seg4 B MT RLO RHI cat TP DP) by (eapply PPgParse4.pp_seg4; eassumption).
assert (S3 : PP_seg3 B MT RLO RHI cat TP DP) by (eapply PPgParse3.pp_seg3; eassumption).
assert (S2L : PP_seg2L B MT RLO RHI cat TP DP) by (eapply PPgParse2L.pp_seg2L; eassumption).
assert (S2 : PP_seg2 B MT RLO RHI cat TP DP) by (eapply PPgParse2.pp_seg2; eassumption).
assert (S1 : PP_seg1 B MT RLO RHI cat TP DP) by (eapply PPgParse1.pp_seg1; eassumption).
assert (S0 : PP_seg0 B MT RLO RHI cat TP DP) by (eapply PPgParse0.pp_seg0; eassumption).
pose proof (S1 (S2 (S2L (S3 S4) S4 0%nat)) S4) as RC1.
unfold tpin_parse_specX.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch sa mo lb s cidm posm cidl posl
  H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16.
exact (S0 RC1 (mkPPCX STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs ch sa mo lb s cidm posm cidl posl
  0 0 (Ereg regs pp_extra))
  (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 (conj H8 (conj H9 (conj H10 (conj H11 (conj H12
   (conj H13 (conj H14 (conj H15 H16)))))))))))))))).
Qed.
(* the Section hypotheses the proof uses (inside the Section they are its assumptions) *)
Print Assumptions pin_pb_parseX.
End b.

Print Assumptions pin_pb_parseX.

(* Image B's instance: the read-only window [0x97c20, 0x99e68) (lib/AU/PPgLib.v RO_LO / RO_HI: pin's
   .data.rel.ro start .. .got end) and the table at PPgSat.PIN_CAT (3256 bytes, 0x98000 .. 0x98cb8) lie in the
   image's third loaded segment (PT_LOAD 0x97bd0, file size 0x2298: .init_array .. .got), so RELRO and CATIMG are
   closed here and never reach the close. The segment step is lib/AU/YCeh.v arodata_ok_journal's, over the same
   window. *)
Lemma pin_relro_img : forall a, 0x97c20 <= a < 0x99e68 -> in_img tfibsegs a.
Proof.
intros a Ha. unfold in_img. eexists. split; [right; right; left; reflexivity|].
match goal with |- Z.le ?lo a /\ Z.lt a (?lo' + ?sz) => let l := eval vm_compute in lo in let h := eval vm_compute in sz in
change lo with l; change sz with h end. lia.
Qed.
Lemma pin_cat_img : forall x, PIN_CAT <= x < PIN_CAT + CAT_BYTES -> in_img tfibsegs x.
Proof. intros x Hx. apply pin_relro_img. unfold PIN_CAT, CAT_BYTES in Hx. lia. Qed.

Section c. Context {fx : YK11.FPState} {rc : YM05.RunCeil}. Context {SK : YI16.sink_head}.
Variable B : asyms.  Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.          Hypothesis MTF : ameter_fs_laws MT.
Hypothesis TL : TfibLib B.                Hypothesis LAWS : AR_laws tfibsegs B.
Hypothesis ML : model_laws (as_universe B).
Hypothesis ASM0 : astack_malloc_realizes tfibsegs B 0.   Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASF : astack_free_law tfibsegs B.             Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis ASTRCSPN : astrcspn_realizes tfibsegs B 0x4191c.
Hypothesis ASTRLEN : astrlen_realizes tfibsegs B 0x41908.
Hypothesis ASTRNCMP : astrncmp_realizes tfibsegs B 0x41914.
Variables TP DP : nat -> Z.
Hypothesis CATALOGUE : tpin_catalogue_specX tfibsegs B MT 0x8107c PIN_CAT.

Theorem pin_pb_parseX_A : tpin_parse_specX tfibsegs B MT 0x97c20 0x99e68 0x80ba4 PIN_CAT 0x20d80 TP DP.
Proof.
eapply pin_pb_parseX.
all: first [ exact pin_relro_img | exact pin_cat_img | eassumption ].
Qed.
End c.

Print Assumptions pin_pb_parseX_A.
