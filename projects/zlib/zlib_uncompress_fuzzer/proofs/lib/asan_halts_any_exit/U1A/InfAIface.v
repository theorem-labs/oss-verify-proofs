(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
(* inflate_state arrays at their 1.4 offsets (lens 168, work 808, codes 1384, sane 7160; 1.3.1: 152, 792, 1368, 7144) *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Bytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Spec Require Import Prelim Monad STree AsanCtrl AsanEmbed AsanProgDeps.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.LibA Require Import ExecF ITreeA SysStepF Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.AsanW Require Import AImg RtCells AProto ABase AMalloc_iface AUri_kit.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U2A Require Import U2AArr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.U1A Require Import U2AObj U2AIface InfABase.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_halts_any_exit.Common Require Import DrvAgree RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition M2 (cx : ictx) (st : ist) : Z := Wm cx st * 134217728 + (c_n cx - t_cin st).
Definition M2e (cx : ictx) : Z := c_W0 cx * 134217728 + (c_n cx - c_cin0 cx).

Definition RA_UW_ZALLOC : Z := 0x93750.
Definition INF_STACK : Z := 672 + 4096 + 4096.

Section CANSEC1. Context {rc : runConstT}.
Section Stmt.
Variable AI : AMallocIface.
Notation CI := (aci AI).
Variable rng_fs : alayout -> footprint -> Prop.

Definition inf_emem (cx : ictx) (Zs : Z) (st : ist) (lf cf wf fo : Z -> Z) (payload : list Z)
    (zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word) (m : amem) : Prop :=
  let S := c_p cx in let D := c_q cx in let n := c_n cx in let OB := c_ob cx in let osz := c_osz cx in
     rw_cells asegs m Zs (strm_cells (Z_to_bv 64 (D + t_cin st)) (Z_to_bv 64 (n - t_cin st)) zti (Z_to_bv 64 (OB + t_cout st))
                                     (Z_to_bv 64 (osz - t_cout st)) zto zmsg (Z_to_bv 64 S) (Z_to_bv 64 A_ZCALLOC) (Z_to_bv 64 A_ZCFREE)
                                     zopq zdt zadl zres zp1 zp2 zp3)
  /\ rw_cells asegs m S (istate_cells (Z_to_bv 64 Zs) (Z_to_bv 64 (t_mode st)) (Z_to_bv 64 (t_last st)) (Z_to_bv 64 5) havedict
                                       (Z_to_bv 64 (t_flags st)) dmax check total (Z_to_bv 64 0) (Z_to_bv 64 15) (Z_to_bv 64 (wsz cx))
                                       (Z_to_bv 64 (t_whave st)) (Z_to_bv 64 (t_wnext st)) (Z_to_bv 64 (c_w cx))
                                       (Z_to_bv 64 (t_hold st)) (Z_to_bv 64 (t_bits st))
                                       (Z_to_bv 64 (t_length st)) (Z_to_bv 64 (t_offset st)) (Z_to_bv 64 (t_extra st))
                                       (Z_to_bv 64 (cp_addrA S (t_lc st))) (Z_to_bv 64 (cp_addrA S (t_dc st)))
                                       (Z_to_bv 64 (t_lb st)) (Z_to_bv 64 (t_db st)) (Z_to_bv 64 (t_ncode st)) (Z_to_bv 64 (t_nlen st))
                                       (Z_to_bv 64 (t_ndist st)) (Z_to_bv 64 (t_shave st)) (Z_to_bv 64 (S + 1384 + 4 * t_nx st)))
  /\ f16arr asegs m (S + 168) 320 lf /\ f16arr asegs m (S + 808) 288 wf /\ f32arr asegs m (S + 1384) 1444 cf
  /\ rw_cells asegs m (S + 7160) (itail_cells (Z_to_bv 64 1) back was pad)
  /\ f8arr asegs m OB (Z.to_nat osz) fo
  /\ bytes_at asegs m D (map (Z_to_bv 8) payload)
  /\ inf_arr_ok cx wf fo
  /\ (exists obr, rw_cells asegs m (OB + osz) [CB (Z.to_nat (262144 - osz)) obr])
  /\ (c_w cx <> 0 -> exists fw, f8arr asegs m (c_w cx) (Z.to_nat 32768) fw).

Definition inf_objs (RNG : footprint) (LB : list ablock) (cx : ictx) (Fu Zs : Z) (payload : list Z) (m : amem) : Prop :=
  let S := c_p cx in let D := c_q cx in let n := c_n cx in let OB := c_ob cx in let osz := c_osz cx in let Wd := c_w cx in
     strm_home LB Fu Zs /\ strm_sh RNG m Fu Zs
  /\ (exists ps, In (HB ps S 7176) LB /\ ((exists pd, In (HB pd D n) LB /\ 0 < n /\ pd <> ps) \/ (n = 0 /\ D = 0x60aca0)))
  /\ (Wd = 0 \/ exists pw, In (HB pw Wd 32768) LB)
  /\ atmost1_c0 LB
  /\ OB = A_OUTBUF /\ 1 <= osz <= 262144 /\ (exists iv, In iv CI /\ fst iv <= OB /\ OB + 262144 <= snd iv)
  /\ shadow_bytes m (Z.shiftr OB 3 + 2147450880) (Z.shiftr OB 3 + 2147450880 + 32768) (fun _ => 0)
  /\ rng RNG OB 262144 /\ rng RNG (Z.shiftr OB 3 + 2147450880) 32768
  /\ 1 <= D /\ 0 <= n < 67108864 /\ D mod 16 = 0 /\ Forall (fun c => 0 <= c < 256) payload /\ Z.of_nat (length payload) = n
  /\ unpoisoned m D (D + n) /\ rng RNG D n /\ rng RNG (Z.shiftr D 3 + 2147450880) (n / 8 + 1)
  /\ u2_tabsh m
  /\ atmost1_c2 LB
  /\ (forall b, In b LB -> ablk (ab_addr b) (ab_addr b + ab_size b))
  /\ (exists iv, In iv CI /\ fst iv <= 141376 /\ 152288 <= snd iv)
  /\ (exists iv, In iv CI /\ fst iv <= 149216 /\ 149568 <= snd iv)
  /\ (Wd <> 0 -> D + n <= Wd \/ Wd + 32768 <= D).

Definition inf_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (stA : astate) (LB : list ablock) (cx : ictx) (Fu Zs lo : Z) (payload : list Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (rcode : Z) (st' : ist) (lf' cf' wf' fo' : Z -> Z)
                    (zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word)
                    (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : amem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 rcode) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             FR (ret_pc ra) fc None m' (seg_rom asegs)
    /\ 0 <= rcode < 18446744073709551616
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ AHEAP AI L RNG stA LB m'
    /\ client_agree AI LB (bv_unsigned sp) (inf_WR cx (ILAY (bv_unsigned sp) 0 Zs 0 lo)) m m'
    /\ inf_objs RNG LB cx Fu Zs payload m'
    /\ ainv cx st' lf' cf' /\ t_mode st' <> MEM
    /\ inf_emem cx Zs st' lf' cf' wf' fo' payload zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m'
    /\ (rcode = 0 -> M2 cx st' < M2e cx) /\ Wm cx st' <= c_W0 cx.

Definition inf_retW (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (FR : bvmap 5 word) (fc : bv 32)
    (s : APS) (LB : list ablock) (cx : ictx) (Fu Zs lo : Z) (payload : list Z) (m : amem)
    (r : option AsanCtrl.aptr) (s' : APS) (RNG' : footprint) : machine_state -> Prop :=
  fun ms' => fp_le RNG RNG' /\ aps_rest s' = aps_rest s /\
    match r with
    | None => False
    | Some pw => exists (Wd : Z),
        Wd mod 16 = 0 /\ ablk Wd (Wd + 32768) /\
        inf_ret L RNG' ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (aps_m s') (HB pw Wd 32768 :: LB) (with_win cx Wd) Fu Zs lo payload m ms'
    end.

Definition inflate_stmtA (haswin : bool) : Prop :=
  forall (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (FR : bvmap 5 word) (fc : bv 32) (m : amem)
         (s : APS) (LB : list ablock) (cx : ictx) (Fu Zs lo : Z) (payload : list Z) (st : ist) (lf cf wf fo : Z -> Z) (tr : list Z)
         (zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad : word),
  AHEAP AI L RNG (aps_m s) LB m ->
  inf_objs RNG LB cx Fu Zs payload m ->
  (if haswin then c_w cx <> 0 else c_w cx = 0) ->
  ainv cx st lf cf -> t_mode st <> MEM -> c_cin0 cx = t_cin st -> c_cout0 cx = t_cout st -> c_W0 cx = Wm cx st ->
  inf_emem cx Zs st lf cf wf fo payload zti zto zmsg zopq zdt zadl zres zp1 zp2 zp3 havedict dmax check total back was pad m ->
  u2_img m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - INF_STACK ->
  bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 < al_top L ->
  mem_inv asegs m ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 Zs -> a1 = Z_to_bv 64 0 ->
  4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
  (haswin = false ->
     uchain m (al_top L) AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) (Nat.pred UDEPTH) tr /\ (length tr <= 27)%nat
     /\ In (AMALLOC_PC :: RA_UW_ZALLOC :: bv_unsigned ra :: tr) (al_U L) /\ bv_unsigned sp + 16 <= bv_unsigned s0) ->
  rng RNG lo (al_top L - lo) -> rng_aimg RNG -> rng_aimg_sh RNG -> rng_fs L RNG ->
  aps_ok L s ->
  evtF asegs RNG
    (fun ms1 =>
         inf_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc (aps_m s) LB cx Fu Zs lo payload m ms1
      \/ (haswin = false /\
          implMA RNG (amalloc_M 32768) s
                 (inf_retW L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 FR fc s LB cx Fu Zs lo payload m) ms1))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        FR (Z_to_bv 64 A_INFLATE) fc None m (seg_rom asegs)).

End Stmt.
End CANSEC1.
