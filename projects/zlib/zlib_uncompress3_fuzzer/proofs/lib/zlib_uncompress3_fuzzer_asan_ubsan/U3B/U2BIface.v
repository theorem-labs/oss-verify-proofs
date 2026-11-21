(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps Harness.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.BothW Require Import BImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U2A Require Import U2AObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.U3B Require Import U2BObj.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.zlib_uncompress3_fuzzer_asan_ubsan.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

Notation rng_aimg_sh RNG := (rng RNG 0x7fffa000 0xc9dbc).

Section CANSEC1. Context {rc : runConstT}.
Definition AVERSION : Z := 0x22760.
Definition AGOT_SHBASE : Z := 0xd16b8.
Definition AGOT_SUAR : Z := 0xd1710.
Definition ASUAR : Z := 0xd9ec0.
Definition AGOT_ZCALLOC : Z := 0xd1cc8.
Definition ASM0 : Z := 0x48804.
Definition ASM1 : Z := 0x48978.
Definition ASM2 : Z := 0x48b08.
Definition AMEMCPY : Z := 0x5d0f8.
Definition AMEMSET : Z := 0x5d594.

Definition RA_INIT_ZALLOC : Z := 0x8dfa4.

Definition SM_STACK : Z := 4096.
Definition INIT_STACK : Z := 112 + 4096.

Definition rt_suar (m : amem) : Prop := rw_cells bsegs m ASUAR [C4 (Z_to_bv 64 1)].

Definition u2_img (m : amem) : Prop :=
     rw_cells bsegs m AGOT_SUAR [C8 (Z_to_bv 64 ASUAR)]
  (* [U14B] A2 2026-11-12: the second conjunct is True at 1.4, as in G's twin U2AIface. 1.3.1
     inflateInit_ loaded zcalloc / zcfree from GOT words at AGOT_ZCALLOC; the 1.4 combined inflateInit_ forms them
     pc-relative (0x8df54 auipc + 0x8df58 add -> 0x95090; 0x8df98 / 0x8df9c -> 0x950a0), and the 1.4 image word at
     0xd1d10 does not hold them (measured: InfB_itcall's vm_compute of that image fact failed in build c1). The
     conjunct is kept, as True, so every (GSU & GZC) pattern still parses. *)
  /\ True.

(* [U14B] A2 2026-11-12: the 1.4 version string at 0x22760 is "1.4" + NUL (4 bytes; objdump -s of the deliver image), so
   its partial-granule shadow byte is 4 (1.3.1: "1.3.1" + NUL, 6); as G's twin U2AIface *)
Definition ver_sh (m : amem) : Prop := shadow_bytes m 2147468524 2147468525 (fun _ => 4).

Definition u2_tabsh (m : amem) : Prop :=
     shadow_bytes m 2147469580 2147469836 (fun _ => 0) /\ shadow_bytes m 2147469900 2147469916 (fun _ => 0)
  /\ shadow_bytes m 2147468552 2147468556 (fun _ => 0) /\ shadow_bytes m 2147468556 2147468557 (fun _ => 6)
  /\ shadow_bytes m 2147469532 2147469539 (fun _ => 0) /\ shadow_bytes m 2147469539 2147469540 (fun _ => 6)
  /\ shadow_bytes m 2147469544 2147469551 (fun _ => 0) /\ shadow_bytes m 2147469551 2147469552 (fun _ => 6)
  /\ shadow_bytes m 2147469556 2147469564 (fun _ => 0) /\ shadow_bytes m 2147469568 2147469576 (fun _ => 0).

Section Stmts.
Variable AI : AMallocIface.
Notation CI := (aci AI).

Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Hypothesis rng_fs_mono : forall L R R', fp_le R R' -> rng_fs L R -> rng_fs L R'.

Notation FB0 F := (mkABlock (ABFake 0) F 64).
Notation FB1 F := (mkABlock (ABFake 1) F 128).
Notation FB2 F := (mkABlock (ABFake 2) F 256).

Hypothesis AI_fake_flag : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st LB m -> In (mkABlock (ABFake cls) F N) LB ->
  rw_cells bsegs m (fflag L cls F) [C1 (Z_to_bv 8 1)] /\ rng RNG (fflag L cls F) 1
  /\ ablk (fflag L cls F) (fflag L cls F + 1) /\ fflag L cls F + 1 <= ATOP
  /\ (forall b, In b LB -> fflag L cls F + 1 <= ab_addr b \/ ab_addr b + ab_size b <= fflag L cls F)
  /\ ~ in_ranges CI (fflag L cls F).
Hypothesis AI_fake_release : forall L RNG st LB m cls F N,
  AHEAP AI L RNG st (mkABlock (ABFake cls) F N :: LB) m ->
  AHEAP AI L RNG st LB (write_to_mem m (wa (fflag L cls F)) [Z_to_bv 8 0]).

Definition sm_post (cls SIZE : Z) (shw : list cell) (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (st : astate) (LB : list ablock) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (F : Z) t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (j0 j1 j2 : word) (junk : list byte),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 F) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aheap_pres CI LB (bv_unsigned sp) m m'
    /\ AHEAP AI L RNG st (mkABlock (ABFake cls) F SIZE :: LB) m'
    /\ F mod SIZE = 0 /\ ablk F (F + SIZE) /\ F + SIZE <= ATOP
    /\ rw_cells bsegs m' F [C8 j0; C8 j1; C8 j2; CB (Z.to_nat (SIZE - 32)) junk; C8 (Z_to_bv 64 (fflag L cls F))]
    /\ rw_cells bsegs m' (shad F) shw
    /\ rng RNG F SIZE /\ rng RNG (shad F) (SIZE / 8).

Definition sm_stmt (ENTRY cls SIZE : Z) (shw : list cell) (NOLIVE : list ablock -> Prop) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (lo : Z),
  AHEAP AI L RNG st LB m ->
  NOLIVE LB ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - SM_STACK ->
  bv_unsigned sp <= al_top L ->
  tp = Z_to_bv 64 ATP ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_fs L RNG ->
  evtF bsegs RNG (sm_post cls SIZE shw L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc st LB lo m)
       (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           FR (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).

Notation Z64 := (C8 (Z_to_bv 64 0)).
Definition no_live (cls : Z) (LB : list ablock) : Prop := forall F n, ~ In (mkABlock (ABFake cls) F n) LB.
Definition atmost1_c2 (LB : list ablock) : Prop :=
  forall F1 n1 F2 n2, In (mkABlock (ABFake 2) F1 n1) LB -> In (mkABlock (ABFake 2) F2 n2) LB -> F1 = F2.

Definition SM0_stmt : Prop := sm_stmt ASM0 0 64 [Z64] (no_live 0).
Definition SM1_stmt : Prop := sm_stmt ASM1 1 128 [Z64; Z64] (no_live 1).
Definition SM2_stmt : Prop := sm_stmt ASM2 2 256 [Z64; Z64; Z64; Z64] atmost1_c2.


Definition strm_home (LB : list ablock) (Fu Zs : Z) : Prop :=
  In (FB2 Fu) LB /\ Zs = Fu + 32 /\ Fu mod 256 = 0 /\ ablk Fu (Fu + 256).
Definition strm_sh (RNG : footprint) (m : amem) (Fu Zs : Z) : Prop :=
  shadow_bytes m (Z.shiftr Zs 3 + 2147450880) (Z.shiftr Zs 3 + 2147450880 + 14) (fun _ => 0)
  /\ rng RNG Zs 112
  /\ wr_at bsegs m (shad Fu) 32 /\ rng RNG (shad Fu) 32.

Definition state_sh (RNG : footprint) (m : amem) (S : Z) : Prop :=
  shadow_bytes m (Z.shiftr S 3 + 2147450880) (Z.shiftr S 3 + 2147450880 + 897) (fun _ => 0)
  /\ rng RNG S 7176 /\ rng RNG (Z.shiftr S 3 + 2147450880) 897.

Definition client_agree (LB : list ablock) (SP : Z) (WR : list (Z * Z)) (m m' : amem) : Prop :=
  magree bsegs (fun a => aclient_addr CI LB SP a /\ ~ in_ranges WR a) m m'.

Definition init_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (Zs lo : Z) (m : amem)
    (next_in avail_in next_out avail_out data_type reserved p1 p2 p3 : word)
    (r : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aps_rest s' = aps_rest s
    /\ client_agree LB (bv_unsigned sp) [(Zs, Zs + 112)] m m'
    /\ match r with
       | None => False
       | Some p => exists S (check len off ext lb db ncode nlen ndist have sane_pad : word) (jarr : list byte) (was pad : word),
           AHEAP AI L RNG' (aps_m s') (HB p S 7176 :: LB) m'
           /\ S mod 16 = 0 /\ ablk S (S + 7176)
           /\ rw_cells bsegs m' Zs (strm_cells next_in avail_in (Z_to_bv 64 0) next_out avail_out (Z_to_bv 64 0) (Z_to_bv 64 0)
                                      (Z_to_bv 64 S) (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) (Z_to_bv 64 0)
                                      (* [U14B] A2 2026-11-12: STATEMENT CHANGE (old: data_type, the caller's value kept).  zlib 1.4's
                                         inflateResetKeep sets strm->data_type = 0; measured: InitB_fin's strm cells at the closing
                                         step of build c19.  The binder data_type stays. *)
                                      (Z_to_bv 64 0)
                                      (Z_to_bv 64 1) reserved p1 p2 p3)
           /\ rw_cells bsegs m' S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 16180) (Z_to_bv 64 0) (Z_to_bv 64 5) (Z_to_bv 64 0)
                                      (Z_to_bv 64 (-1)) (Z_to_bv 64 32768) check (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 15)
                                      (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 0)
                                      len off ext (Z_to_bv 64 (S + 1384)) (Z_to_bv 64 (S + 1384)) lb db ncode nlen ndist have
                                      (Z_to_bv 64 (S + 1384)))
           /\ rw_cells bsegs m' (S + 168) [CB (Z.to_nat 6992) jarr]
           /\ rw_cells bsegs m' (S + 7160) (itail_cells (Z_to_bv 64 1) (Z_to_bv 64 (-1)) was pad)
       end.

Definition inflateInit_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem)
         (s : APS) (LB : list ablock) (Fu Zs lo : Z) (tr : list Z)
         (next_in avail_in total_in next_out avail_out total_out msg state opaque data_type adler reserved p1 p2 p3 : word),
  AHEAP AI L RNG (aps_m s) LB m ->
  strm_home LB Fu Zs -> strm_sh RNG m Fu Zs ->
  rw_cells bsegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg state
                                  (Z_to_bv 64 0) (Z_to_bv 64 0) opaque data_type adler reserved p1 p2 p3) ->
  u2_img m -> ver_sh m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - INIT_STACK ->
  bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 Zs -> a1 = Z_to_bv 64 AVERSION -> a2 = Z_to_bv 64 112 ->
  4096 <= bv_unsigned ra ->
  bv_unsigned sp + 16 < al_top L ->
  In [AMALLOC_PC; RA_INIT_ZALLOC] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG ->
  aps_ok L s ->
  implMA RNG (amalloc_M 7176) s
         (init_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB Zs lo m
                    next_in avail_in next_out avail_out data_type reserved p1 p2 p3)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 A_INFLATEINIT) fc None m (seg_rom bsegs)).

Definition RA_END_ZFREE_W : Z := 0x94f78.
Definition RA_END_ZFREE_S : Z := 0x94fa8.
Definition END_STACK : Z := 64 + 4096.

Definition end_post (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB' : list ablock) (Zs lo : Z) (m : amem)
    (next_in avail_in total_in next_out avail_out total_out msg opaque data_type adler reserved p1 p2 p3 : word)
    (r : unit) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\
    exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ aps_rest s' = aps_rest s
    /\ client_agree LB' (bv_unsigned sp) [(Zs, Zs + 112)] m m'
    /\ AHEAP AI L RNG' (aps_m s') LB' m'
    /\ rw_cells bsegs m' Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 0)
                                        (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3).

Definition inflateEnd_stmtA (withwin : bool) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem)
         (s : APS) (LB : list ablock) (Fu Zs S Wd lo : Z) (pw ps : AsanCtrl.aptr) (mode : Z)
         (next_in avail_in total_in next_out avail_out total_out msg opaque data_type adler reserved p1 p2 p3 : word)
         (last wrap havedict flags dmax check total head wbits wsize whave wnext hold bits
          length offset extra lencode distcode lenbits distbits ncode nlen ndist have next : word),
  AHEAP AI L RNG (aps_m s) LB m ->
  strm_home LB Fu Zs -> strm_sh RNG m Fu Zs ->
  In (HB ps S 7176) LB ->
  (if withwin then In (HB pw Wd 32768) LB else Wd = 0) ->
  rw_cells bsegs m Zs (strm_cells next_in avail_in total_in next_out avail_out total_out msg (Z_to_bv 64 S)
                                  (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE) opaque data_type adler reserved p1 p2 p3) ->
  rw_cells bsegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 mode) last wrap havedict flags dmax check total head wbits wsize whave wnext
                                   (Z_to_bv 64 Wd) hold bits length offset extra lencode distcode lenbits distbits ncode nlen ndist have next) ->
  16180 <= mode <= 16211 ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - END_STACK ->
  bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 Zs ->
  bv_unsigned sp + 16 < al_top L ->
  (if withwin then In [AFREE_PC; RA_END_ZFREE_W] (al_U L) else True) -> In [AFREE_PC; RA_END_ZFREE_S] (al_U L) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG ->
  aps_ok L s ->
  implMA RNG (free_all afree_M (if withwin then [pw; ps] else [ps])) s
         (end_post L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s
                   (if withwin then lb_remove ps (lb_remove pw LB) else lb_remove ps LB) Zs lo m
                   next_in avail_in total_in next_out avail_out total_out msg opaque data_type adler reserved p1 p2 p3)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (Z_to_bv 64 A_INFLATEEND) fc None m (seg_rom bsegs)).

End Stmts.
End CANSEC1.
