(* check_round_trip (fs.asan-ubsan 0x81b9c, build B), WALK LANE D2: the chain of segments 34-39, the B twin.
   This file composes the six segment lemmas of the lane into its one exported step,
   `crt_from SK B crt_ss34 (crt_INV_822ac B)` - lane D1 hands over at crt_INV_822ac (0x82408 on B, the return of
   fuzz_free (file); A 0x822ac) and the tail takes over at crt_INV_T (0x824b4 on B, the return of free (same); A
   0x82354), where lib/B/FSH_crt_segD.v's crt_tail is already proved.

   rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from 6cf61486dca lib/A/FSH_crt_segD2_top.v)
   rule 24: proves no function (kind: segment lemmas of check_round_trip's walk, PORTED from 1ab57ca7ad7) - RT : CrtRt B
   (not FsRt) (a working branch 1ab57ca7ad7).
   Port source: a working branch 6cf61486dca proofs/omx-clap-core/fuzz_state/lib/A/FSH_crt_segD2_top.v, itself
   PORTED from a working branch d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_chain.v
   (`st_chain`, its St19..St24 part). Same names and statements as the A file; the B content is in the six segment
   files and the kit lib/B/FSH_crt_segD2.v. Imports: lib.A.X -> lib.B.X where lib/B/X.v exists (AB1v -> YB1v,
   AB1w -> YB1w, AE2k -> YE2k); SetShadowDefU, FSupoison, FSupoisonU, FSH_YC20 and FSH_Gen stay lib/A's. A's import of
   lib/A/FSW_malloc_free.v is dropped: this file uses nothing from it, and neither lib/A nor lib/B of this tree has it.
   A new file: no licence lines.

   The chain, each link a file of this lane (B pcs, A in brackets):
     crtD2_seg34  FSH_crt_segD2_s34.v  0x82408 -> 0x82410 [0x822ac -> 0x822b4]  pj_free (&back)
                                                                     crt_INV_822ac -> crtD2_INV_35
     crtD2_seg35  FSH_crt_segD2_s35.v  0x82410 -> 0x82418 [0x822b4 -> 0x822bc]  pj_free (&doc)   crtD2_INV_35 -> _36
     crtD2_seg36  FSH_crt_segD2_s36.v  0x82418 -> 0x8249c [0x822bc -> 0x8233c]  29 shadow stores + fuzz_free (back)
                                                                     crtD2_INV_36 -> _37
     crtD2_seg37  FSH_crt_segD2_s37.v  0x8249c -> 0x824a4 [0x8233c -> 0x82344]  fuzz_free (text)  crtD2_INV_37 -> _38
     crtD2_seg38  FSH_crt_segD2_s38.v  0x824a4 -> 0x824ac [0x82344 -> 0x8234c]  free (want)       crtD2_INV_38 -> _39
     crtD2_seg39  FSH_crt_segD2_s39.v  0x824ac -> 0x824b4 [0x8234c -> 0x82354]  free (same)       crtD2_INV_39 -> crt_INV_T
   and the tail, already proved in FSH_crt_segD.v, is crt_tail. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP03 YP0l YP0k YP06 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YG05 YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import YB1v YB1w.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
SetShadowDefU FSupoison FSupoisonU FSH_YC20 FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require Import
FSH_Base FSH_Rt FSPstat FSW_K FSW_rres FSW_ret FSW_frame
FSW_frame3 FSW_crt_tbl FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt FSH_crt_base FSH_crt_site
FSH_crt_segD FSH_crt_segD2 FSH_crt_segD2_s34 FSH_crt_segD2_s35 FSH_crt_segD2_s36 FSH_crt_segD2_s37
FSH_crt_segD2_s38 FSH_crt_segD2_s39.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.B Require YE2k.
Import ListNotations.
Local Open Scope Z_scope.

Section top. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
(* the callee contracts the six calls consume (READER's pj_free at level 0, ALLOC's fuzz_free, RUNTIME's CrtRt for the
   two __wrap_free thunks), and the image / environment / model facts of B (RELOC discharges them in the final
   instance) - nothing else *)
Hypothesis PJ_FREE : @pj_free_spec fx rc SK tfibsegs B 0.
Hypothesis FUZZ_FREE : @fuzz_free_spec fx rc SK tfibsegs B.
Hypothesis RT : CrtRt B.
Hypothesis HENV : api_env tfibsegs B.
Hypothesis IMG : fs_img_facts tfibsegs B.
Hypothesis ML : model_laws (as_universe B).

(* ---- the lane's step: the walk from the tail's entry (0x824b4, crt_INV_T) back to the return of fuzz_free (file)
   (0x82408), across the six frees ---- *)
Lemma crtD2_main :
  crt_from SK B crt_ssT (crt_INV_T B) -> crt_from SK B crt_ss34 (crt_INV_822ac B).
Proof.
intros HT.
exact (crtD2_seg34 SK B PJ_FREE IMG (crtD2_seg35 SK B PJ_FREE IMG
  (crtD2_seg36 SK B FUZZ_FREE IMG (crtD2_seg37 SK B FUZZ_FREE IMG
  (crtD2_seg38 SK B RT HENV IMG ML (crtD2_seg39 SK B RT HENV IMG ML HT)))))).
Qed.

(* ---- and with the tail (FSH_crt_segD.v's crt_tail, already proved from crt_INV_T): the whole walk from 0x82408
   to check_round_trip's `ret` (0x8261c), under the tail's three runtime laws ---- *)
Hypothesis ASF : astack_free_law tfibsegs B.
Hypothesis FFL : frame_flag_lawP tfibsegs B.
Hypothesis SETSH : crt_set_shadow_fixed B PC_set_shadow_f5 0xf5.
Lemma crtD2_from_822ac : crt_from SK B crt_ss34 (crt_INV_822ac B).
Proof. exact (crtD2_main (crt_tail SK B ASF FFL SETSH)). Qed.
End top.
