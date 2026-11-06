(* preset_base64_decode (fs.asan, image A): the two closing theorems, from the three stage lemmas. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00 YI0n.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_alloc FSH_Fn_writer
FSW_K FSW_K3 FSW_ret FSW_rres FSW_strkit FSW_writer_tbl FSW_writer_model
FSW_dec_defs FSW_dec_E FSW_dec_F FSW_dec_L4 FSW_dec_L5 FSW_dec_L FSW_dec_top.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.

Section F. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
(* The callee contracts are S0's (FSH_Fn_alloc fuzz_malloc_spec / fuzz_free_spec; FSH_Gen astrlen_realizesU /
   amemchr_realizesU, RUNTIME's interceptors at fs.asan's PC_strlen / PC_memchr); HIMG is FSH_Rt's image interface.
   The three stages are proved: entry (FSW_dec_E), loop (FSW_dec_L, over the memchr arm FSW_dec_L4 and the NUL arm
   FSW_dec_L5, both placements of *lenp), free (FSW_dec_F). Neither theorem takes anything more. *)
Theorem decode_holds : forall B, FsShadowSyms B -> fs_img_facts tfibsegs B ->
  astrlen_realizesU tfibsegs B PC_strlen -> amemchr_realizesU tfibsegs B PC_memchr ->
  fuzz_malloc_spec tfibsegs B -> fuzz_free_spec tfibsegs B ->
  decode_spec B tfibsegs.
Proof.
intros B HSS HIMG HSTRLEN HMEMCHR HMALLOC HFREE.
apply (decode_of_stages B).
- exact (dec_entry_ok_stage B HSS HIMG HSTRLEN HMALLOC).
- exact (dec_loop_stage B HSS HIMG HMEMCHR).
- exact (dec_free_stage B HSS HFREE).
Qed.

Theorem decode_ff_holds : forall B, FsShadowSyms B -> fs_img_facts tfibsegs B ->
  astrlen_realizesU tfibsegs B PC_strlen -> amemchr_realizesU tfibsegs B PC_memchr ->
  fuzz_malloc_spec tfibsegs B -> fuzz_free_spec tfibsegs B ->
  decode_spec_ff B tfibsegs.
Proof.
intros B HSS HIMG HSTRLEN HMEMCHR HMALLOC HFREE.
apply (decode_ff_of_stages B).
- exact (dec_entry_ok_stage B HSS HIMG HSTRLEN HMALLOC).
- exact (dec_loop_stage B HSS HIMG HMEMCHR).
- exact (dec_free_stage B HSS HFREE).
Qed.
End F.
