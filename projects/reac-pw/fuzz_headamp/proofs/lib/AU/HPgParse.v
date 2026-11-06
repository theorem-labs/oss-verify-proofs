(* Modified by Theorem Labs, 2026-10: the composition step of proofs/reac-pw/fuzz_role/lib/A/RPgParse.v at afaa3cb55c1
   (rl_parse_A: the walk's segment theorems applied to the composition lemma) for reac-pw/fuzz_headamp's image B. *)
(* reac-pw/fuzz_headamp image B (fuzz_headamp.asan-ubsan, pinned sha256
   53edda9bdeeba1803865babfecb1af6732babe47ab83c64d38cc59a90d717a94): the two tops of the parse.
   - hd_parse_result_B: lib/A/HPgCSpec.v's hd_parse_result_specX at reac_headamp_prop_parse_result 0x849ac with image
     B's literals (lib/AU/HPgImgB.v headamp_himg_B: "reac.headamp." 0x214a0, "phantom" 0x214c0, "pad" 0x214e0, "sens"
     0x21500, the stack-guard cells 0x9d478 / 0x5f8210, the four read-only doubles), for every read-only window
     RLO .. RHI: lib/AU/HPgParseJoin.v's hp_join_B applied to the eight segment theorems of lib/AU/HPgParse{E,F,W,K,
     V,X}.v.
   - hd_parse_B: hd_parse_specX at reac_headamp_prop_parse 0x849a4 from hd_parse_result_B (lib/AU/HPgParseWrapB.v).
   Proves function reac_headamp_prop_parse_result and reac_headamp_prop_parse of image B, under the Section hypotheses
   below, each discharged where its owner proves it: the symbol record's .got / shadow-cell / errno fields and api_env
   at image B's start-up symbol record (lib/AU/YF0m.v; errno: ts_errno, TFIB_ERRNO = 0x5d812c), the meter laws at the
   meter of record, the three wrapper contracts in hole form (lib/A/HPgHole.v:480 / :524 / :573) by the wrapper port
   lanes at image B's trampolines 0x41c24 / 0x41ca8 / 0x41c20. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0s YK15 YK18 YP09 YI04 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgHole HPgParseBase.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require Import Img0U HPgImgB HPgParseCut HPgParseJoin HPgParseWrapB.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.AU Require HPgParseE HPgParseF HPgParseW HPgParseK HPgParseV HPgParseX.
Import ListNotations.
Open Scope Z_scope.

Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = PB_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = PB_SH_CELL.
Hypothesis errno_low : api_env rsegs B.
Hypothesis HBerrno : as_errno B = 0x5d812c.
Hypothesis STRNCMP : forall F fc, hd_astrncmp_hole (fx := mkFP F fc) rsegs B B_TRAMP_STRNCMP.
Hypothesis STRTOL : forall F fc, hd_astrtol_hole (fx := mkFP F fc) rsegs B B_TRAMP_STRTOL (hi_gotw headamp_himg_B)
  (hi_guard headamp_himg_B).
Hypothesis STRCMP : forall F fc, hd_astrcmp_hole (fx := mkFP F fc) rsegs B B_TRAMP_STRCMP.

Theorem hd_parse_result_B : forall RLO RHI : Z,
hd_parse_result_specX rsegs B MT B_PARSE_RESULT RLO RHI (hi_akey headamp_himg_B) (hi_aph headamp_himg_B)
  (hi_apad headamp_himg_B) (hi_asens headamp_himg_B) (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B)
  (hi_dcs headamp_himg_B).
Proof.
apply hp_join_B.
- apply HPgParseE.segE_ok; assumption.
- apply HPgParseX.segEPI_ok; assumption.
- apply HPgParseX.segEXIT_ok; assumption.
- apply HPgParseF.segFIND_ok; assumption.
- apply HPgParseW.segWALK_ok; assumption.
- apply HPgParseW.segADV_ok; assumption.
- apply HPgParseK.segKEY_ok; assumption.
- apply HPgParseV.segVAL_ok; assumption.
Qed.

Theorem hd_parse_B : forall RLO RHI : Z,
hd_parse_specX rsegs B MT PB_WRAP RLO RHI (hi_akey headamp_himg_B) (hi_aph headamp_himg_B)
  (hi_apad headamp_himg_B) (hi_asens headamp_himg_B) (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B)
  (hi_dcs headamp_himg_B).
Proof. intros RLO RHI. apply hp_parse_of_result_B. apply hd_parse_result_B. Qed.

(* The same at the read-only window RLO = RHI = 0 (the window occurs only in hd_parse_args' arodata_okP; the empty
   window is the weakest premise, so these are the strongest forms; the assembly takes these by name). *)
Corollary hd_parse_result_B00 :
hd_parse_result_specX rsegs B MT B_PARSE_RESULT 0 0 (hi_akey headamp_himg_B) (hi_aph headamp_himg_B)
  (hi_apad headamp_himg_B) (hi_asens headamp_himg_B) (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B)
  (hi_dcs headamp_himg_B).
Proof. exact (hd_parse_result_B 0 0). Qed.
Corollary hd_parse_B00 :
hd_parse_specX rsegs B MT PB_WRAP 0 0 (hi_akey headamp_himg_B) (hi_aph headamp_himg_B)
  (hi_apad headamp_himg_B) (hi_asens headamp_himg_B) (hi_gotw headamp_himg_B) (hi_guard headamp_himg_B)
  (hi_dcs headamp_himg_B).
Proof. exact (hd_parse_B 0 0). Qed.
End f.

Print Assumptions hd_parse_result_B.
Print Assumptions hd_parse_B.
Print Assumptions hd_parse_result_B00.
Print Assumptions hd_parse_B00.
Check hd_parse_result_B00.
Check hd_parse_B00.
