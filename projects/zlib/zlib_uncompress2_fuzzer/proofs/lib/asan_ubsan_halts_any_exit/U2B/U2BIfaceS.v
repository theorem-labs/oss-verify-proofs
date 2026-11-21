(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps Harness.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2A Require Import U2AArr U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.U2B Require Import U2BObj U2BIface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.asan_ubsan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Definition uw_next (wsize wnext whave copy : Z) : Z * Z :=
  let wn := if wsize =? 0 then 0 else wnext in
  let wh := if wsize =? 0 then 0 else whave in
  if 32768 <=? copy then (0, 32768)
  else let dist := Z.min (32768 - wn) copy in
       if copy - dist =? 0
       then ((if wn + dist =? 32768 then 0 else wn + dist), (if wh <? 32768 then wh + dist else wh))
       else (copy - dist, 32768).

Section CANSEC1. Context {rc : runConstT}.
Definition RA_UW_ZALLOC : Z := 0x94920.
Definition UW_STACK : Z := 112 + 4096.

Definition outbuf_ok (m : amem) : Prop :=
  (exists obs, rw_cells bsegs m A_OUTBUF [CB (Z.to_nat 262144) obs])
  /\ shadow_bytes m (Z.shiftr A_OUTBUF 3 + 2147450880) (Z.shiftr A_OUTBUF 3 + 2147450880 + 32768) (fun _ => 0)
  /\ wr_at bsegs m (shad A_OUTBUF) 32768.

Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Definition outbuf_client : Prop := exists iv, In iv CI /\ fst iv <= A_OUTBUF /\ A_OUTBUF + 262144 <= snd iv.

Definition uw_post_core (L : alayout) (RNG' : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st' : astate) (LB' : list ablock) (S Wd Zs lo : Z) (m : amem) (LB : list ablock)
    (mode : Z) (last wrap havedict flags dmax check total head hold bits
     length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word)
    (wn' wh' : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (wbytes' : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ client_agree AI LB (bv_unsigned sp) [(S + 68, S + 96); (Wd, Wd + 32768)] m m'
    /\ AHEAP AI L RNG' st' LB' m'
    /\ rw_cells bsegs m' S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head (Z_to_bv 64 15)
                                        (Z_to_bv 64 32768) (Z_to_bv 64 wh') (Z_to_bv 64 wn')
                                        (Z_to_bv 64 Wd) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next)
    /\ rw_cells bsegs m' Wd [CB (Z.to_nat 32768) wbytes'].

Definition updatewindow_old_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem)
         (st : astate) (LB : list ablock) (Fu Zs S Wd lo : Z) (pw ps : AsanCtrl.aptr) (mode cout copy wn wh : Z)
         (next_in avail_in total_in next_out avail_out total_out msg opaque data_type adler reserved p1 p2 p3 : word)
         (last wrap havedict flags dmax check total head hold bits
          length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word) (wbytes : list byte),
  AHEAP AI L RNG st LB m ->
  strm_home LB Fu Zs -> strm_sh RNG m Fu Zs ->
  In (HB ps S 7176) LB -> In (HB pw Wd 32768) LB ->
  rw_cells bsegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                  (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3) ->
  rw_cells bsegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head (Z_to_bv 64 15)
                                   (Z_to_bv 64 32768) (Z_to_bv 64 wh) (Z_to_bv 64 wn)
                                   (Z_to_bv 64 Wd) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next) ->
  rw_cells bsegs m Wd [CB (Z.to_nat 32768) wbytes] ->
  outbuf_ok m ->
  0 <= copy <= cout -> cout <= 262144 -> 0 <= wn < 32768 -> 0 <= wh <= 32768 ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - UW_STACK ->
  bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 < al_top L ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 Zs -> a1 = Z_to_bv 64 (A_OUTBUF + cout) -> a2 = Z_to_bv 64 copy ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
  evtF bsegs RNG (uw_post_core L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB S Wd Zs lo m LB
                               mode last wrap havedict flags dmax check total head hold bits
                               length offset extra lencode distcode lenbits distbits ncode nlen ndist have next
                               (fst (uw_next 32768 wn wh copy)) (snd (uw_next 32768 wn wh copy)))
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 A_UPDATEWINDOW) fc None m (seg_rom bsegs)).

Definition uw_new_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (S Zs lo : Z) (m : amem)
    (mode : Z) (last wrap havedict flags dmax check total head hold bits
     length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word) (copy : Z)
    (r : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ aps_rest s' = aps_rest s /\
    match r with
    | None => False
    | Some pw => exists Wd,
        Wd mod 16 = 0 /\ ablk Wd (Wd + 32768)
        /\ uw_post_core L RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (aps_m s') (HB pw Wd 32768 :: LB) S Wd Zs lo m LB
                        mode last wrap havedict flags dmax check total head hold bits
                        length offset extra lencode distcode lenbits distbits ncode nlen ndist have next
                        (fst (uw_next 0 0 0 copy)) (snd (uw_next 0 0 0 copy)) ms'
    end.

Definition updatewindow_new_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem)
         (s : APS) (LB : list ablock) (Fu Zs S lo : Z) (ps : AsanCtrl.aptr) (mode cout copy : Z) (tr : list Z)
         (next_in avail_in total_in next_out avail_out total_out msg opaque data_type adler reserved p1 p2 p3 : word)
         (last wrap havedict flags dmax check total head whave wnext hold bits
          length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word),
  AHEAP AI L RNG (aps_m s) LB m ->
  strm_home LB Fu Zs -> strm_sh RNG m Fu Zs ->
  In (HB ps S 7176) LB ->
  outbuf_client ->
  rw_cells bsegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                  (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3) ->
  rw_cells bsegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head (Z_to_bv 64 15)
                                   (Z_to_bv 64 0) whave wnext
                                   (Z_to_bv 64 0) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next) ->
  outbuf_ok m ->
  0 <= copy <= cout -> cout <= 262144 ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - UW_STACK ->
  bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 Zs -> a1 = Z_to_bv 64 (A_OUTBUF + cout) -> a2 = Z_to_bv 64 copy ->
  bv_unsigned sp + 16 < al_top L ->
  In [AMALLOC_PC; RA_UW_ZALLOC] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
  aps_ok L s ->
  implMA RNG (amalloc_M 32768) s
         (uw_new_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB S Zs lo m
                      mode last wrap havedict flags dmax check total head hold bits
                      length offset extra lencode distcode lenbits distbits ncode nlen ndist have next copy)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 A_UPDATEWINDOW) fc None m (seg_rom bsegs)).

End Stmts.
End CANSEC1.
