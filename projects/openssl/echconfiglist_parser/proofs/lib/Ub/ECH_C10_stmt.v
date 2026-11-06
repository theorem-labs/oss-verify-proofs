(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ub Require Import USegs RMalloc_iface_stmt HeapSR_iface ECH_Img ECH_Xpres ECH_Rep ECH_LibState ECH_C1_stmt.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim STree Malloc Prog.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition FR_PACKET_memdup : Z := 64.   Definition FR_PACKET_strndup : Z := 48.
Definition PKMEMDUP_STACK : Z := FR_PACKET_memdup + Z.max CMEMDUP_STACK 16.
Definition PKSTRNDUP_STACK : Z := FR_PACKET_strndup + CSTRNDUP_STACK.

(* [comment removed for export] *)
Definition apart (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.
(* [comment removed for export] *)
Definition cells_apart (a b : Z) : Prop := apart a 8 b 8.

Section W.
  Variable H : hsr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pkmemdup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (pkt cur ms : Z) (bs : list byte) (dptr lptr lo B : Z) (m : mem) (mo : Model) (v : Z) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (LB' : list block) (D : Z),
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ hs_RHEAP H s' LB' m'
      /\ rw_cells usegs m' pkt (pk_cells cur ms (zlength bs))
      /\ rw_cells usegs m' dptr [C8 (wz D)] /\ rw_cells usegs m' lptr [C8 (wz (if zlength bs =? 0 then 0 else zlength bs))]
      /\ ( (zlength bs = 0 /\ D = 0 /\ LB' = LB)
         \/ (1 <= zlength bs /\ exists p, rblock_range D (zlength bs) /\ LB' = (p, D, zlength bs) :: LB
             /\ rw_cells usegs m' D [CB (length bs) bs]) )
      /\ xpres LB (bv_unsigned sp) ([(dptr, dptr + 8); (lptr, lptr + 8)] ++ memflag_foot) m m'
      /\ (exists v', MEMFLAG m' v' /\ v <= v') /\ IMPL_mem m' /\ GOT_mem m'.         (* [comment removed for export] *)
  Definition pkmemdup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (pkt cur ms dptr lptr oldlen v lo B : Z) (bs : list byte) (errv : word),
      a0 = Z_to_bv 64 pkt -> a1 = Z_to_bv 64 dptr -> a2 = Z_to_bv 64 lptr ->
      pkt mod 8 = 0 -> dptr mod 8 = 0 -> lptr mod 8 = 0 ->   (* [comment removed for export] *)
      rw_cells usegs m pkt (pk_cells cur ms (zlength bs)) -> bv_unsigned sp <= pkt ->
      rw_cells usegs m dptr [C8 (wz 0)] -> rw_cells usegs m lptr [C8 (wz oldlen)] -> cells_apart dptr lptr ->
      outcell_ok LB (bv_unsigned sp) B dptr -> outcell_ok LB (bv_unsigned sp) B lptr ->
      apart pkt 24 dptr 8 -> apart pkt 24 lptr 8 -> apart cur (zlength bs) dptr 8 -> apart cur (zlength bs) lptr 8 ->
      bytes_at usegs m cur bs -> xclient_range LB (bv_unsigned sp) memflag_foot cur (zlength bs) -> zlength bs < 0x7ffffffb ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + zlength bs <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB + big1 (zlength bs) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - PKMEMDUP_STACK ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      hs_SR H (pkmemdup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB pkt cur ms bs dptr lptr lo B m mo v)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_PACKET_memdup) fc None m (seg_rom usegs)) mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pkstrndup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : PState) (LB : list block) (pkt cur ms : Z) (bs : list byte) (dptr lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : PState) (D : Z) (p : bptr),
      let k := strnlen bs in
      cfg_ms c = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom usegs)
      /\ hs_KREL H s' (cfg_model c) /\ hs_MPRES H mo (cfg_model c)
      /\ mem_inv usegs m' /\ stk usegs m' lo (bv_unsigned sp)
      /\ rw_cells usegs m' (errno_addr tp) [C4 errv'] /\ hs_rauxv_ok H m' B
      /\ rblock_range D (Z.of_nat k + 1) /\ hs_RHEAP H s' ((p, D, Z.of_nat k + 1) :: LB) m'
      /\ rw_cells usegs m' D [CB k (firstn k bs); C1 (b8 0)]
      /\ rw_cells usegs m' pkt (pk_cells cur ms (zlength bs))
      /\ rw_cells usegs m' dptr [C8 (wz D)]
      /\ xpres LB (bv_unsigned sp) ((dptr, dptr + 8) :: memflag_foot) m m'
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'.
  Definition pkstrndup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : PState) (LB : list block)
           (pkt cur ms dptr v lo B : Z) (bs : list byte) (errv : word),
      a0 = Z_to_bv 64 pkt -> a1 = Z_to_bv 64 dptr ->
      pkt mod 8 = 0 -> dptr mod 8 = 0 -> cur + zlength bs < 2^64 ->   (* [comment removed for export] *)
      rw_cells usegs m pkt (pk_cells cur ms (zlength bs)) -> bv_unsigned sp <= pkt -> 0 < cur < 2^64 ->
      rw_cells usegs m dptr [C8 (wz 0)] -> outcell_ok LB (bv_unsigned sp) B dptr ->
      apart pkt 24 dptr 8 -> apart cur (zlength bs) dptr 8 ->
      bytes_at usegs m cur bs -> xclient_range LB (bv_unsigned sp) memflag_foot cur (zlength bs) -> zlength bs < 2^31 ->
      hs_RHEAP H s LB m -> hs_KREL H s mo ->
      lb_bytes LB + (zlength bs + 1) <= hs_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= hs_LIVE_CNT_MAX H -> lb_big LB + big1 (zlength bs + 1) <= hs_LIVE_BIG_MAX H ->
      hs_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk usegs m lo (bv_unsigned sp) -> hceil <= lo -> lo <= bv_unsigned sp - PKSTRNDUP_STACK ->
      rw_cells usegs m (errno_addr tp) [C4 errv] -> mem_inv usegs m -> tp = Z_to_bv 64 RATP ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      hs_SR H (pkstrndup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB pkt cur ms bs dptr lo B m mo)
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 P_PACKET_strndup) fc None m (seg_rom usegs)) mo).

  Definition C10_stmts : Prop := pkmemdup_stmt /\ pkstrndup_stmt.
End W.

End HCW.
