(* rule 24: proves no function (kind: segment lemma of check_round_trip's walk, PORTED from a working branch
   d25a984c903 proofs/omx-clap-core/fuzz_state/lib/A/Prog/check_round_trip_sd16.v (the stretch from pj_parse's return
   through the second decode and the bcmp to fuzz_free, crt16_runA :392 / crt16_runB :541), check_round_trip_sd17.v and
   check_round_trip_sd18.v (the two fuzz_free stages St17 :521 / St18 :535 of check_round_trip_stdefs.v)). The checker's
   CONFIRM for the walk (a Theorem Labs lane, role check, 2026-10-29 04:3xZ) is on the lane head
   (internal path), lines 6-21: the hit's Require closure is 334 files with 0
   Admitted / Axiom / Parameter. Only the stage structure is ported; the statements are the S0 forms of
   FSH_crt_base.v (crt_from, crt_INV_82268, crt_INV_822ac).

   check_round_trip 0x81a9c, fs.asan (sha256 64b53ff86172bb07...), LANE D1: the lane's one deliverable, segments 30-33
   chained backwards from the lane's exit at 0x822ac (crt_INV_822ac, which lane D2 starts from) to its entry at 0x82268
   (crt_INV_82268, where lane C2 ends):
     segment 33  fuzz_free (file)   crtD1_seg33  (FSH_crt_segD1_free.v)
     segment 32  fuzz_free (got)    crtD1_seg32  (FSH_crt_segD1_free.v)
     segment 31  bcmp, or the empty-body arm straight to fuzz_free (got)
                                    crtD1_seg31  (FSH_crt_segD1_s31.v), its empty-body arm's call crtD1_freez
     segment 30  preset_base64_decode (z, &n)
                                    crtD1_seg30  (FSH_crt_segD1_dec.v)
   The Section hypotheses are the callee contracts the lane calls (DECODE, FUZZ_FREE, RT for the bcmp thunk) with the
   image's api_env (HENV). The decode's room premise crt_room_D1 is no hypothesis: segment 30 takes it from
   FSH_crt_room.crt_room_D1_holds (base v33's by-trace budgets), and the frees pay their ticks from the invariants'
   remaining allowance. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_reader FSH_Fn_writer FSH_Fn_alloc FSH_Fn_crt
FSH_crt_base FSH_crt_site FSH_crt_segD1 FSH_crt_segD1_inv FSH_crt_segD1_dec FSH_crt_segD1_s31 FSH_crt_segD1_free.
Import ListNotations.
Open Scope Z_scope.

Section main. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable SK : YI16.sink_head.
Variable B : asyms.
Hypothesis DECODE : @FSH_Fn_writer.decode_spec_ff fx rc SK B tfibsegs.
Hypothesis FUZZ_FREE : @fuzz_free_spec fx rc SK tfibsegs B.
Hypothesis RT : CrtRt B.
Hypothesis HENV : api_env tfibsegs B.

(* lane D1, 0x82268 -> 0x822ac *)
Lemma crtD1_main :
  crt_from SK B (crt_ss_ret 0x822ac crt_cs1 crt_csF) (crt_INV_822ac B) ->
  crt_from SK B (crt_ss_ret 0x82268 crt_cs1 crt_csF) (crt_INV_82268 B).
Proof.
intros H34.
pose proof (crtD1_seg33 SK B FUZZ_FREE H34) as H33.
pose proof (crtD1_seg32 SK B FUZZ_FREE H33) as H32.
pose proof (crtD1_seg31 SK B RT HENV (crtD1_freez SK B FUZZ_FREE) H32 H33) as H31.
exact (crtD1_seg30 SK B DECODE H31).
Qed.
End main.
About crtD1_main.
Print Assumptions crtD1_main.
