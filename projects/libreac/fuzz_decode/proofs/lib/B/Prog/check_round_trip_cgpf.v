(* check_round_trip_cgpf: the close of the cgif-form walk of check_round_trip, image B (fuzz_decode.asan-ubsan,
   original pin), onto the fixed statement lib/B/Prog/check_round_trip_cg.v dec_check_round_trip_cg_holds_stmt
   (frozen at a working branch 53b4b22c7c2, merged).

   The five pieces of lib/B/Prog/crtB_cuts.v compose by crtB_holds_of_cuts, at RO_RD := DEC_RO_RD, the statement's
   read set.  The pieces (all theorems; their lanes' branches merged, never rebased):
     crtB_entry        lib/B/Prog/crtB_w_entry.v  (CRT_ENTRY .. CRT_RET_CALLOC; a Theorem Labs lane, merged 878750f14bc)
     crtB_setup        lib/B/Prog/crtB_w_setup.v  (CRT_RET_CALLOC .. CRT_LOOP_IN)
     crtB_loop         lib/B/Prog/crtB_loop.v     (CRT_LOOP_IN .. CRT_LOOP_OUT; a Theorem Labs lane, merged 7c8d5076f53)
     crtB_encbcmp      lib/B/Prog/crtB_encbcmp.v  (CRT_LOOP_OUT .. CRT_RET_BCMP, at DEC_RO_RD; lane EncBcmp, merged
                       2a389df9ac1; leaves of record 39c43113162)
     crtB_tail         lib/B/Prog/crtB_tail.v     (CRT_RET_BCMP .. dec_crt_post; lane CrtTail, merged 342aea58c22)
   dec_check_round_trip_cg_holds has no premise beyond the statement's own. *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YK11 YK0s YK0o YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable Require Import YG00 YG01 YG0f YG0n YG0d YCbq YC5d YGCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeTFIB.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B Require Import DecodeCalloc.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import DecodeBSyms DecodeBAddr.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require reac_braid_encode_cg.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import check_round_trip_cg crtB_cuts.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crtB_w_entry crtB_w_setup crtB_loop crtB_encbcmp.
From OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog Require Import crtB_tail.
Import ListNotations.
Open Scope Z_scope.
Module YKK := OSSVerify.Proofs.libreac.fuzz_decode.lib.Reusable.YK11.
Module LBraidC := OSSVerify.Proofs.libreac.fuzz_decode.lib.B.Prog.reac_braid_encode_cg.

Section Close.
Context {fx : YKK.FPState} {rc : YM05.RunCeil}.
Local Notation sink := dec_B_sink_head.
Local Notation segs := decodesegsB0.
Variable B : asyms.
Variable MT : ameter_ops.

(* The scoped read-only fact the cuts carry, at the statement's read set, from the statement's own lemma
   dec_ro_rd_scoped and its two instance facts on B (no lane hypothesis). *)
Lemma crtB_ro_scoped_dec : dec_ro_rd_unowned B -> dec_rom_no_errno B -> crtB_ro_scoped B DEC_RO_RD.
Proof.
  intros HO HE. unfold crtB_ro_scoped. intros a Hin0. unfold crtB_in_ro_rd in Hin0.
  destruct Hin0 as (r & Hin & Hr). apply (dec_ro_rd_scoped B HO HE a).
  unfold dec_in_ro_rd. apply Exists_exists. exists r. split; [exact Hin | exact Hr].
Qed.

(* At RO_RD := DEC_RO_RD the cuts' read set is the statement's. *)
Lemma crtB_ro_sub_dec : crtB_ro_sub DEC_RO_RD.
Proof.
  unfold crtB_ro_sub. intros a Hin0. unfold crtB_in_ro_rd in Hin0. destruct Hin0 as (r & Hin & Hr).
  unfold dec_in_ro_rd. apply Exists_exists. exists r. split; [exact Hin | exact Hr].
Qed.

(* The statement (lib/B/Prog/check_round_trip_cg.v dec_check_round_trip_cg_holds_stmt), from the five pieces. *)
Theorem dec_check_round_trip_cg_holds : forall CTX : list (list Z), @dec_check_round_trip_cg_holds_stmt fx rc B MT CTX.
Proof.
  intros CTX. unfold dec_check_round_trip_cg_holds_stmt.
  intros HM HF HC HO HNE HAR HML HU HUF RM RF RC RB RE.
  exact (@crtB_holds_of_cuts fx rc B MT DEC_RO_RD (@crtB_entry fx rc B MT DEC_RO_RD) (@crtB_setup fx rc B MT DEC_RO_RD)
           (@crtB_loop rc B MT DEC_RO_RD) (@crtB_encbcmp rc B MT) (@crtB_tail rc B MT DEC_RO_RD)
           CTX (crtB_ro_scoped_dec HO HNE) crtB_ro_sub_dec HM HF HC HAR HML HU HUF RM RF RC RB RE).
Qed.
End Close.
