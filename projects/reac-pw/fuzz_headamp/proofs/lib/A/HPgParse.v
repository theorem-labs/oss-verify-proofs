(* reac-pw/fuzz_headamp's ASan image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47; unstripped twin
   b5f352154c54a97c66fd92dfa228e8a854498f6cd313dba0107900546b043f9a, the same loaded bytes except .note.gnu.build-id): the walks of
   reac_headamp_prop_parse_result 0x845b4 and of its 8-byte wrapper reac_headamp_prop_parse 0x845ac against
   lib/A/HPgCSpec.v's hd_parse_result_specX and hd_parse_specX. Proves function reac_headamp_prop_parse_result (written
   new) and reac_headamp_prop_parse (ported).

   The parse_result walk is the eight segment theorems of lib/A/HPgParseE.v (entry), HPgParseEX.v (EPI, EXIT),
   HPgParseFind.v (FIND), HPgParseWalk.v (WALK, ADV), HPgParseKey.v (KEY) and HPgParseVal.v (VAL), joined by
   lib/A/HPgParseJoin.v's hp_join_A (induction on the find loop's and the pair loop's fuel), at every read-only window
   RLO .. RHI and, by name, at RLO = RHI = 0. The wrapper is lib/A/HPgParseWrap.v's hp_parse_of_result_A (two steps,
   then the parse at res = 0).

   Section hypotheses (each discharged where the symbol record B and the meter MT are fixed): MTL (the meter's laws),
   HBgot / HBcell (the .got word 0x9c370 holds the shadow-offset cell 0xa4db8: AR's constant law at image A's record),
   errno_low (YCbq.v api_env: the errno cell in the image, apart from the frames), HBerrno (image A's errno cell
   0x5d7cac, the record's ts_errno), and the three string wrappers' contracts in the frame-hole form of lib/A/HPgHole.v
   at image A's trampolines 0x41ba4 (strncmp), 0x41c28 (strtol, with the stack-guard cells 0x9cff8 / 0x5f7d90) and
   0x41ba0 (strcmp), for every float state. *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import Img0 HPgBase HPgCSpec HPgImgA HPgHole.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgParseBase HPgParseCut HPgParseJoin.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require
  HPgParseE HPgParseEX HPgParseFind HPgParseWalk HPgParseKey HPgParseVal HPgParseWrap.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.

Section b. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis MTL : ameter_laws MT.
Hypothesis HBgot : as_got_shadow B = PA_GOT_SH.
Hypothesis HBcell : as_shadow_cell B = PA_SH_CELL.
Hypothesis errno_low : api_env rsegs B.
Hypothesis HBerrno : as_errno B = 0x5d7cac.
Hypothesis STRNCMP : forall F fc, hd_astrncmp_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRNCMP.
Hypothesis STRTOL : forall F fc, hd_astrtol_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRTOL
  (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A).
Hypothesis STRCMP : forall F fc, hd_astrcmp_hole (fx := mkFP F fc) rsegs B A_TRAMP_STRCMP.

(* reac_headamp_prop_parse_result 0x845b4, every read-only window *)
Theorem hd_parse_result_A : forall RLO RHI : Z,
hd_parse_result_specX rsegs B MT A_PARSE_RESULT RLO RHI (hi_akey headamp_himg_A) (hi_aph headamp_himg_A)
  (hi_apad headamp_himg_A) (hi_asens headamp_himg_A) (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A)
  (hi_dcs headamp_himg_A).
Proof.
apply hp_join_A.
- eapply HPgParseE.hp_segE_A; eassumption.
- eapply HPgParseEX.hp_segEPI_A; eassumption.
- eapply HPgParseEX.hp_segEXIT_A; eassumption.
- eapply HPgParseFind.hp_segFIND_A; eassumption.
- eapply HPgParseWalk.hp_segWALK_A; eassumption.
- eapply HPgParseWalk.hp_segADV_A; eassumption.
- eapply HPgParseKey.hp_segKEY_A; eassumption.
- eapply HPgParseVal.hp_segVAL_A; eassumption.
Qed.

(* the same at the read-only window RLO = RHI = 0, the form the image's assembly applies *)
Theorem hd_parse_result_A00 :
hd_parse_result_specX rsegs B MT A_PARSE_RESULT 0 0 (hi_akey headamp_himg_A) (hi_aph headamp_himg_A)
  (hi_apad headamp_himg_A) (hi_asens headamp_himg_A) (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A)
  (hi_dcs headamp_himg_A).
Proof. exact (hd_parse_result_A 0 0). Qed.

(* reac_headamp_prop_parse 0x845ac, every read-only window *)
Theorem hd_parse_A : forall RLO RHI : Z,
hd_parse_specX rsegs B MT PA_WRAP RLO RHI (hi_akey headamp_himg_A) (hi_aph headamp_himg_A)
  (hi_apad headamp_himg_A) (hi_asens headamp_himg_A) (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A)
  (hi_dcs headamp_himg_A).
Proof. intros RLO RHI. apply HPgParseWrap.hp_parse_of_result_A. exact (hd_parse_result_A RLO RHI). Qed.

Theorem hd_parse_A00 :
hd_parse_specX rsegs B MT PA_WRAP 0 0 (hi_akey headamp_himg_A) (hi_aph headamp_himg_A)
  (hi_apad headamp_himg_A) (hi_asens headamp_himg_A) (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A)
  (hi_dcs headamp_himg_A).
Proof. exact (hd_parse_A 0 0). Qed.

End b.

Print Assumptions hd_parse_result_A.
Print Assumptions hd_parse_result_A00.
Print Assumptions hd_parse_A.
Print Assumptions hd_parse_A00.
