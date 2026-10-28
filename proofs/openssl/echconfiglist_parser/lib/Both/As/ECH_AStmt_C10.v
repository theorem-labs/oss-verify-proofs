(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Arr SysStep Exec CellsX TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AsConst AsIface AsIfaceX AsCXXHeap ECH_AImg ECH_Xpres ECH_ARep ECH_ALib ECH_Iface ECH_AStmt_C1.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prelim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.

Definition FR_PACKET_memdup : Z := 80.   Definition FR_PACKET_strndup : Z := 48.    (* [comment removed for export] *)
Definition PKMEMDUP_STACK : Z := FR_PACKET_memdup + Z.max CMEMDUP_STACK CFREE_STACK.
Definition PKSTRNDUP_STACK : Z := FR_PACKET_strndup + Z.max CSTRNDUP_STACK CFREE_STACK.
Definition PF_pkmemdup : list (Z * list Z) := pf_shift R_PACKET_memdup_CRYPTO_memdup PF_cmemdup.
Definition PF_pkstrndup : list (Z * list Z) := pf_shift R_PACKET_strndup_CRYPTO_strndup PF_cstrndup.

(* [comment removed for export] *)
Definition apart (a n b k : Z) : Prop := a + n <= b \/ b + k <= a.
(* [comment removed for export] *)
Definition cells_apart (a b : Z) : Prop := apart a 8 b 8.

Section W.
  Variable H : asr.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pkmemdup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (pkt cur ms : Z) (bs : list byte) (dptr lptr lo B : Z) (m : mem) (mo : Model) (v : Z) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (LB' : list block) (D : Z),
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ as_RHEAP H s' LB' m' /\ as_RFS H LF m'
      /\ rw_cells asegs m' pkt (pk_cells cur ms (zlength bs))
      /\ rw_cells asegs m' dptr [C8 (wz D)] /\ rw_cells asegs m' lptr [C8 (wz (if zlength bs =? 0 then 0 else zlength bs))]
      /\ ( (zlength bs = 0 /\ D = 0 /\ LB' = LB /\ as_AL H s' >= as_AL H s - as_Cf H 0)
         \/ (1 <= zlength bs /\ exists p, ablock_range H D (zlength bs) /\ LB' = (p, D, zlength bs) :: LB
             /\ rw_cells asegs m' D [CB (length bs) bs] /\ addressable m' D (zlength bs)
             /\ as_AL H s' >= as_AL H s - as_Cf H 0 - as_Cm H (zlength bs)) )
      /\ xpres H LB (bv_unsigned sp) ([(pkt, pkt + 24); (dptr, dptr + 8); (lptr, lptr + 8)] ++ memflag_foot) m m'
      /\ (exists v', MEMFLAG m' v' /\ v <= v') /\ IMPL_mem m' /\ GOT_mem m'.         (* [comment removed for export] *)
  Definition pkmemdup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (bC : block) (pkt cur ms dptr lptr oldlen v lo B : Z) (bs : list byte) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_PACKET_memdup) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 pkt -> a1 = Z_to_bv 64 dptr -> a2 = Z_to_bv 64 lptr ->
      rw_cells asegs m pkt (pk_cells cur ms (zlength bs)) -> ashobj H LB (bv_unsigned sp) pkt 24 -> pkt + 24 <= B ->
      rw_cells asegs m dptr [C8 (wz 0)] -> rw_cells asegs m lptr [C8 (wz oldlen)] -> cells_apart dptr lptr ->
      ashobj H LB (bv_unsigned sp) dptr 8 -> ashobj H LB (bv_unsigned sp) lptr 8 ->
      apart pkt 24 dptr 8 -> apart pkt 24 lptr 8 -> apart cur (zlength bs) dptr 8 -> apart cur (zlength bs) lptr 8 -> apart cur (zlength bs) pkt 24 ->
      bytes_at asegs m cur bs -> In bC LB -> blk_addr bC <= cur -> cur + zlength bs <= blk_addr bC + blk_size bC -> zlength bs <= 2^28 ->
      (* [comment removed for export] *)
      pkt mod 8 = 0 -> dptr mod 8 = 0 -> lptr mod 8 = 0 ->
      (* [comment removed for export] *)
      as_RFS H LF m -> afs_write_ok H LF (dptr, dptr + 8) -> afs_write_ok H LF (lptr, lptr + 8) ->
      accessible m pkt 24 -> accessible m dptr 8 -> accessible m lptr 8 -> accessible m cur (zlength bs) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + zlength bs <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - PKMEMDUP_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> offchain CH dptr 8 -> offchain CH lptr 8 ->
      pf_ok (as_TR H) PF_pkmemdup (bv_unsigned ra) CH -> as_Cf H 0 + as_Cm H (zlength bs) <= as_AL H s ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      as_SR H (pkmemdup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF pkt cur ms bs dptr lptr lo B m mo v) (mkCfg msF mo).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pkstrndup_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB : list block) (LF : list fframe) (pkt cur ms : Z) (bs : list byte) (dptr lo B : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun c => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (errv' : word) (s' : as_St H) (D : Z) (p : bptr),
      let k := strnlen bs in
      as_VIS H s' (cfg_ms c) = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ as_AKREL H s' c /\ as_MPRES H mo (cfg_model c)
      /\ mem_inv asegs m' /\ ACONST m' /\ stk asegs m' lo (bv_unsigned sp)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B
      /\ ablock_range H D (Z.of_nat k + 1) /\ as_RHEAP H s' ((p, D, Z.of_nat k + 1) :: LB) m' /\ as_RFS H LF m'
      /\ rw_cells asegs m' D [CB k (firstn k bs); C1 (b8 0)] /\ addressable m' D (Z.of_nat k + 1)
      /\ rw_cells asegs m' pkt (pk_cells cur ms (zlength bs))
      /\ rw_cells asegs m' dptr [C8 (wz D)]
      /\ xpres H LB (bv_unsigned sp) ([(pkt, pkt + 24); (dptr, dptr + 8)] ++ memflag_foot) m m'
      /\ MEMFLAG m' 1 /\ IMPL_mem m' /\ GOT_mem m'
      /\ as_AL H s' >= as_AL H s - as_Cf H 0 - as_Cm H (Z.of_nat k + 1).
  Definition pkstrndup_stmt : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block) (LF : list fframe)
           (bC : block) (pkt cur ms dptr v lo B : Z) (bs : list byte) (errv : word) (CH : list (Z * Z)),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 P_PACKET_strndup) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 pkt -> a1 = Z_to_bv 64 dptr ->
      rw_cells asegs m pkt (pk_cells cur ms (zlength bs)) -> ashobj H LB (bv_unsigned sp) pkt 24 -> pkt + 24 <= B -> 0 < cur < 2^64 ->
      rw_cells asegs m dptr [C8 (wz 0)] -> ashobj H LB (bv_unsigned sp) dptr 8 ->
      apart pkt 24 dptr 8 -> apart cur (zlength bs) dptr 8 -> apart cur (zlength bs) pkt 24 ->
      bytes_at asegs m cur bs -> In bC LB -> blk_addr bC <= cur -> cur + zlength bs <= blk_addr bC + blk_size bC -> zlength bs < 2^28 ->
      (* [comment removed for export] *)
      pkt mod 8 = 0 -> dptr mod 8 = 0 ->
      (* [comment removed for export] *)
      as_RFS H LF m -> afs_write_ok H LF (dptr, dptr + 8) ->
      accessible m pkt 24 -> accessible m dptr 8 -> accessible m cur (zlength bs) ->
      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) ->
      lb_bytes LB + (zlength bs + 1) <= as_LIVE_MAX H -> Z.of_nat (length LB) + 1 <= as_LIVE_CNT_MAX H ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - PKSTRNDUP_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned sp mod 16 = 0 -> ACONST m ->
      as_chain H m (bv_unsigned s0) CH -> (forall fp' ra', In (fp', ra') CH -> bv_unsigned sp + 16 <= fp') -> pf_ok (as_TR H) PF_pkstrndup (bv_unsigned ra) CH -> as_Cf H 0 + as_Cm H (zlength bs + 1) <= as_AL H s ->
      MEMFLAG m v -> IMPL_mem m -> GOT_mem m ->
      as_SR H (pkstrndup_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF pkt cur ms bs dptr lo B m mo) (mkCfg msF mo).

  Definition C10_stmts : Prop := pkmemdup_stmt /\ pkstrndup_stmt.
End W.

End HCW.
