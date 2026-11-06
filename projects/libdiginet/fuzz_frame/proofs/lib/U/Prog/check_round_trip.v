(* check_round_trip in fuzz_frame.ubsan meets its contract U/Prog/check_round_trip_c.v, with the contracts of its callees as premises (check_round_trip_holds). *)
(* check_round_trip in fuzz_frame.ubsan (0x131e4, fuzz/fuzz_frame.c:114-200) meets its contract
   U/Prog/check_round_trip_c.v, with the contracts of its callees as premises: malloc and free of
   the allocator (U/Contract.v), memset, bcmp (the kit's libc contracts), diginet_frame_build
   (U/Prog/diginet_frame_build_c.v) and spec_build_frame (U/Prog/spec_build_frame_c.v). The walk:
   crt_top.v (the SR phases with malloc and free) over the instruction segments crt_segs.v,
   crt_mid.v (crt_m1.v, crt_m2.v, crt_m3.v) and crt_shy.v, stated in crt_defs.v. The UBSan twin
   of Prog/check_round_trip.v. *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YK11 YK0o YK0s YK15 YM06 YP09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YO0i YO0f YO0d YO05
YO0p YO0j YO0m YO0l YO0n YO0k YO0o YO09.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Reusable Require Import YM05 YL0i YL01.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U Require Import Contract Img0.
From OSSVerify.Proofs.libdiginet.fuzz_frame.lib.U.Prog Require Import check_round_trip_c crt_defs crt_top
  crt_segs crt_mid crt_m1 crt_m2 crt_m3 crt_shy memset_c bcmp_c diginet_frame_build_c spec_build_frame_c.
Import ListNotations.
Local Open Scope Z_scope.

Section CRT.
Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable B : malloc_syms.
Variable API : AllocAPI B.

Theorem check_round_trip_holds :
  ms_malloc B = 0x14f2c -> ms_free B = 0x14dec -> errno_addr B + 4 <= alloc_ceiling ->
  AllocExtra B (aa_MR API) -> ctx_owned B API ->
  (forall fx' : YK11.FPState, @malloc_contract fx' rc B API) ->
  (forall fx' : YK11.FPState, @free_contract fx' rc B API) ->
  memset_contract -> bcmp_contract -> diginet_frame_build_contract -> spec_build_frame_contract ->
  check_round_trip_contract B API.
Proof.
  intros MALPC FREEPC ERR AX CT MALLOC FREE MEMSET BCMP BUILD SBF.
  intros L A regs mem md w buf b sb SEGS.
  exact (crt_holds B API SEGS MALPC FREEPC ERR AX CT MALLOC FREE MEMSET BCMP BUILD SBF
    crt_seg1_ok crt_seg2_ok (crt_mid_of crt_m1_ok crt_m2_ok crt_m3_ok) crt_shy_ok crt_segf1_ok crt_segf2_ok
    crt_segx_ok L A regs mem md w buf b sb SEGS).
Qed.

End CRT.
