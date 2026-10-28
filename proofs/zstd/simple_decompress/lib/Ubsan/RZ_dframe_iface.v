(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdDctxRep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_frame_iface RZ_block_iface.
Import ListNotations.
Open Scope Z_scope.

Definition wz0 : word := Z_to_bv 64 0.
Definition h5_frame_ok (ws : list word) : Prop :=
  wnth ws H5_format = wz0 /\ wnth ws H5_forceIgnoreChecksum = wz0 /\ wnth ws H5_refMultipleDDicts = wz0 /\
  wnth ws H5_maxBlockSizeParam = wz0 /\ wnth ws H5_customAlloc = wz0 /\ wnth ws H5_customFree = wz0 /\
  wnth ws H5_customOpaque = wz0 /\ wnth ws H5_staticSize = wz0 /\ wnth ws H5_ddictLocal = wz0 /\ wnth ws H5_ddict = wz0 /\
  wnth ws H5_dictUses = wz0 /\ wnth ws H5_ddictSet = wz0 /\ wnth ws H5_inBuff = wz0.

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation DECODEFH_STACK := 128 (only parsing).

Definition zd_decodefh_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DCTX : Z) (src : list Z) (off hsz : Z) (pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (lo : Z) (m : fmem)
    : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' fp' pcs' xs' ws',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (decode_frame_header src off hsz)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DCTX + 29928, DCTX + 29984); (DCTX + 30008, DCTX + 30116); (SPV - DECODEFH_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ dctx_fp usegs m' DCTX fp' /\ dctx_h3 usegs m' DCTX pcs' dsz bt stg le fe
    /\ dctx_xs usegs m' DCTX xs' /\ dctx_h5 usegs m' DCTX ws'
    /\ match get_frame_header src off hsz with
       | FH_ok h => fp' = zfh_cells h
                    /\ pcs' = Z_to_bv 64 (bv_unsigned pcs + hsz)
                    /\ ws' = wupd ws H5_validateChecksum (Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1))
                    /\ (if fh_checksum h =? 0 then xs' = xs else exists j1 j2, xs' = xxh_cells j1 0 j2)
       | FH_ret _ => pcs' = pcs /\ xs' = xs /\ ws' = ws
       end.

Definition zd_decodefh_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV DCTX SRC : Z) (src : list Z) (off hsz : Z)
         (fp : list cell) (pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (lo : Z),
  dctx_fp usegs m DCTX fp -> dctx_h3 usegs m DCTX pcs dsz bt stg le fe -> dctx_xs usegs m DCTX xs ->
  dctx_h5 usegs m DCTX ws -> h5_frame_ok ws ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 ->
  bytes_at usegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= off -> 5 <= hsz -> off + hsz <= zlen src -> 0 < SRC ->
  stk usegs m lo SPV -> lo <= SPV - DECODEFH_STACK -> 0 <= SPV < 2^64 ->
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 (SRC + off) -> a2 = Z_to_bv 64 hsz ->
  evt usegs (zd_decodefh_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX src off hsz pcs dsz bt stg le fe xs ws lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_DECODEFH) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation DBEGIN_STACK := 64 (only parsing).
Notation PZD_GOT_TRACE := 0x36e40 (only parsing).

Definition zd_dbegin_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DCTX : Z) (ws : list word) (jhb : list byte) (ovd dcb dce : word) (lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
              (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992); (SPV - DBEGIN_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ dctx_ptrs usegs m' DCTX (Z_to_bv 64 (DCTX + 32)) (Z_to_bv 64 (DCTX + 6192)) (Z_to_bv 64 (DCTX + 4136)) (Z_to_bv 64 (DCTX + 10296))
    /\ dctx_h1 usegs m' DCTX wz0 wz0 wz0 wz0 (Z_to_bv 64 5)
    /\ dctx_h3 usegs m' DCTX wz0 wz0 (Z_to_bv 64 3) wz0 wz0 wz0
    /\ dctx_h5 usegs m' DCTX (wupd (wupd ws H5_isFrameDecompression (Z_to_bv 64 1)) H5_dictID wz0)
    /\ dctx_tx usegs m' DCTX jhb ovd dcb dce wz0
    /\ dctx_owned usegs m' DCTX
    /\ bytes_at usegs m' (DCTX + 10296) (le4 (Z_to_bv 64 201326604))
    /\ bytes_at usegs m' (DCTX + 26684) (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8)).

Definition zd_dbegin_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV DCTX : Z)
         (llt mlt oft huf pde pfx vst dend expd pcs dsz bt stg le fe : word) (ws : list word) (jhb : list byte) (ovd dcb dce trace gend : word) (lo : Z),
  dctx_ptrs usegs m DCTX llt mlt oft huf -> dctx_h1 usegs m DCTX pde pfx vst dend expd ->
  dctx_h3 usegs m DCTX pcs dsz bt stg le fe -> dctx_h5 usegs m DCTX ws -> h5_frame_ok ws ->
  dctx_tx usegs m DCTX jhb ovd dcb dce trace -> dctx_owned usegs m DCTX ->
  rw_cells usegs m PZD_GOT_TRACE [C8 gend; C8 wz0] ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 -> DCTX mod 8 = 0 ->
  stk usegs m lo SPV -> lo <= SPV - DBEGIN_STACK -> 0 <= SPV < 2^64 ->
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (PZD_GOT_TRACE + 16 <= lo \/ SPV <= PZD_GOT_TRACE) ->
  (PZD_GOT_TRACE + 16 <= DCTX \/ DCTX + 95992 <= PZD_GOT_TRACE) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = wz0 -> a2 = wz0 ->
  evt usegs (zd_dbegin_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX ws jhb ovd dcb dce lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_DBEGIN) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_checkcont_post (ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (DCTX DST dsize : Z) (expd : word) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists a0 a2 a3 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DCTX + 29888, DCTX + 29920)] m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ (if (DST =? 0) || (dsize =? 0)
        then dctx_h1 usegs m' DCTX wz0 wz0 wz0 wz0 expd
        else dctx_h1 usegs m' DCTX (Z_to_bv 64 DST) (Z_to_bv 64 DST) (Z_to_bv 64 DST) wz0 expd).

Definition zd_checkcont_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (DCTX DST dsize : Z) (expd : word),
  dctx_h1 usegs m DCTX wz0 wz0 wz0 wz0 expd ->
  0 < DCTX -> DCTX mod 8 = 0 -> DCTX + 95992 < 2^64 -> 0 <= DST < 2^64 -> 0 <= dsize < 2^64 ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 dsize ->
  evt usegs (zd_checkcont_post ra sp gp tp t0 t1 t2 s0 s1 a1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc DCTX DST dsize expd m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_CHECKCONT) fc None m (seg_rom usegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Notation DMF_STACK := 2368 (only parsing).    (* [comment removed for export] *)

Definition dctx_any (m : fmem) (DCTX : Z) : Prop :=
  exists llt mlt oft huf pde pfx vst dend expd fp pcs dsz bt stg le fe xs ws jhb ovd dcb dce trace,
    dctx_ptrs usegs m DCTX llt mlt oft huf /\ dctx_h1 usegs m DCTX pde pfx vst dend expd /\ dctx_fp usegs m DCTX fp /\
    dctx_h3 usegs m DCTX pcs dsz bt stg le fe /\ dctx_xs usegs m DCTX xs /\ dctx_h5 usegs m DCTX ws /\ h5_frame_ok ws /\
    dctx_tx usegs m DCTX jhb ovd dcb dce trace /\ dctx_owned usegs m DCTX.

Definition zd_dmf_post (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV DCTX DST CAP : Z) (src : list Z) (size lo : Z) (m : fmem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch [(DCTX, DCTX + 95992); (DST, DST + CAP); (SPV - DMF_STACK, SPV)] m m'
    /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo SPV
    /\ dctx_any m' DCTX
    /\ stk usegs m' DST (DST + CAP)
    /\ 0 <= r < 2^64 /\ (zd_is_error r = false -> decompress_ok src size CAP r).

Definition zd_dmf_stmt : Prop :=
  forall (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : fmem) (SPV lo DCTX DST CAP SRC : Z) (src : list Z) (size : Z),
  dctx_any m DCTX -> 4096 <= DCTX -> DCTX + 95992 < 2^47 -> DCTX mod 8 = 0 ->
  rw_cells usegs m PZD_GOT_TRACE [C8 wz0; C8 wz0] ->
  bytes_at usegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= size -> size <= zlen src -> size < 2^40 ->
  4096 <= SRC -> SRC + zlen src < 2^47 ->
  stk usegs m DST (DST + CAP) -> 0 <= CAP -> CAP < 2^40 -> (DST = 0 -> CAP = 0) -> (DST <> 0 -> 4096 <= DST) -> DST + CAP < 2^47 ->
  stk usegs m lo SPV -> 4096 <= lo -> lo <= SPV - DMF_STACK -> SPV < 2^47 -> SPV mod 16 = 0 ->
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (DST + CAP <= lo \/ SPV <= DST) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (PZD_GOT_TRACE + 16 <= lo \/ SPV <= PZD_GOT_TRACE) ->
  (DST + CAP <= DCTX \/ DCTX + 95992 <= DST) -> (DST + CAP <= SRC \/ SRC + zlen src <= DST) ->
  (SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC) ->
  (PZD_GOT_TRACE + 16 <= DCTX \/ DCTX + 95992 <= PZD_GOT_TRACE) -> (PZD_GOT_TRACE + 16 <= DST \/ DST + CAP <= PZD_GOT_TRACE) ->
  mem_inv usegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 SRC -> a4 = Z_to_bv 64 size ->
  a5 = wz0 -> a6 = wz0 -> a7 = wz0 ->
  evt usegs (zd_dmf_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP src size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PZD_DMF) fc None m (seg_rom usegs)).
