(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit ZdFrameW ZdDctxRep DrvAgree.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg RtCells AProto ABase AMalloc_iface AFake_iface AZ_kit AZ_globals AZ_globalsR AZ_frame_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Notation DECODEFH_STACK_A := 4608 (only parsing).
Notation DBEGIN_STACK_A := 2400 (only parsing).   (* [comment removed for export] *)
Notation CHECKCONT_STACK_A := 16 (only parsing).   (* [comment removed for export] *)
Notation APZD_GOT_TRACE := 0xc7fd0 (only parsing).   (* [comment removed for export] *)
Notation DECODEFH_DEPTH := 2 (only parsing).
Notation DMF_DEPTH := 7 (only parsing).
Notation DMF_STACK_A := 7184 (only parsing).   (* [comment removed for export] *)

Section CANSEC1. Context {rc : runConstT}.

Definition wz0 : word := Z_to_bv 64 0.
Definition h5_frame_ok (ws : list word) : Prop :=
  wnth ws H5_format = wz0 /\ wnth ws H5_forceIgnoreChecksum = wz0 /\ wnth ws H5_refMultipleDDicts = wz0 /\
  wnth ws H5_maxBlockSizeParam = wz0 /\ wnth ws H5_customAlloc = wz0 /\ wnth ws H5_customFree = wz0 /\
  wnth ws H5_customOpaque = wz0 /\ wnth ws H5_staticSize = wz0 /\ wnth ws H5_ddictLocal = wz0 /\ wnth ws H5_ddict = wz0 /\
  wnth ws H5_dictUses = wz0 /\ wnth ws H5_ddictSet = wz0 /\ wnth ws H5_inBuff = wz0.

(* [comment removed for export] *)
(* [comment removed for export] *)





(* [comment removed for export] *)
(* [comment removed for export] *)

Definition zd_dbegin_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV DCTX : Z) (ws : list word) (jhb : list byte) (ovd dcb dce : word) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(DCTX, DCTX + 32); (DCTX + 10296, DCTX + 10300); (DCTX + 26684, DCTX + 26696); (DCTX + 29888, DCTX + 29928);
              (DCTX + 29976, DCTX + 30008); (DCTX + 30096, DCTX + 30372); (DCTX + 95940, DCTX + 95992); (SPV - DBEGIN_STACK_A, SPV)] m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ dctx_ptrs bsegs m' DCTX (Z_to_bv 64 (DCTX + 32)) (Z_to_bv 64 (DCTX + 6192)) (Z_to_bv 64 (DCTX + 4136)) (Z_to_bv 64 (DCTX + 10296))
    /\ dctx_h1 bsegs m' DCTX wz0 wz0 wz0 wz0 (Z_to_bv 64 5)
    /\ dctx_h3 bsegs m' DCTX wz0 wz0 (Z_to_bv 64 3) wz0 wz0 wz0
    /\ dctx_h5 bsegs m' DCTX (wupd (wupd ws H5_isFrameDecompression (Z_to_bv 64 1)) H5_dictID wz0)
    /\ dctx_tx bsegs m' DCTX jhb ovd dcb dce wz0
    /\ dctx_owned bsegs m' DCTX
    /\ bytes_at bsegs m' (DCTX + 10296) (le4 (Z_to_bv 64 201326604))
    /\ bytes_at bsegs m' (DCTX + 26684) (le4 (Z_to_bv 64 1) ++ le4 (Z_to_bv 64 4) ++ le4 (Z_to_bv 64 8)).

Definition zd_dbegin_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV DCTX : Z)
         (llt mlt oft huf pde pfx vst dend expd pcs dsz bt stg le fe : word) (ws : list word) (jhb : list byte) (ovd dcb dce trace gend : word) (lo : Z),
  dctx_ptrs bsegs m DCTX llt mlt oft huf -> dctx_h1 bsegs m DCTX pde pfx vst dend expd ->
  dctx_h3 bsegs m DCTX pcs dsz bt stg le fe -> dctx_h5 bsegs m DCTX ws -> h5_frame_ok ws ->
  dctx_tx bsegs m DCTX jhb ovd dcb dce trace -> dctx_owned bsegs m DCTX ->
  rw_cells bsegs m APZD_GOT_TRACE [C8 wz0; C8 gend] ->      (* [comment removed for export] *)
  4096 <= DCTX -> DCTX + 95992 < 2^47 ->
  stk bsegs m lo SPV -> lo <= SPV - DBEGIN_STACK_A -> 0 <= SPV < 2^64 -> SPV < 2^47 ->   (* [comment removed for export] *)
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (APZD_GOT_TRACE + 16 <= lo \/ SPV <= APZD_GOT_TRACE) ->
  (APZD_GOT_TRACE + 16 <= DCTX \/ DCTX + 95992 <= APZD_GOT_TRACE) ->
  (* [comment removed for export] *)
  DCTX mod 8 = 0 -> areg RNG m DCTX 95992 -> ahull RNG m DCTX 95992 -> art m -> astk RNG lo SPV ->
  aro_client RNG m ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = wz0 -> a2 = wz0 ->
  evtF bsegs RNG (zd_dbegin_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX ws jhb ovd dcb dce lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_DBEGIN) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zd_checkcont_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (SPV DCTX DST dsize : Z) (expd : word) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(DCTX + 29888, DCTX + 29920); (SPV - CHECKCONT_STACK_A, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ (if (DST =? 0) || (dsize =? 0)
        then dctx_h1 bsegs m' DCTX wz0 wz0 wz0 wz0 expd
        else dctx_h1 bsegs m' DCTX (Z_to_bv 64 DST) (Z_to_bv 64 DST) (Z_to_bv 64 DST) wz0 expd).

Definition zd_checkcont_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV DCTX DST dsize : Z) (expd : word) (lo : Z),
  dctx_h1 bsegs m DCTX wz0 wz0 wz0 wz0 expd ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 -> 0 <= DST < 2^64 -> 0 <= dsize < 2^64 ->
  stk bsegs m lo SPV -> lo <= SPV - CHECKCONT_STACK_A -> SPV < 2^47 -> (DCTX + 95992 <= lo \/ SPV <= DCTX) ->
  (* [comment removed for export] *)
  0 < DCTX -> DCTX mod 8 = 0 -> areg RNG m (DCTX + 29888) 32 -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 dsize ->
  evtF bsegs RNG (zd_checkcont_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST dsize expd lo m)
       (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 APZD_CHECKCONT) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition dctx_any (m : amem) (DCTX : Z) : Prop :=
  exists llt mlt oft huf pde pfx vst dend expd fp pcs dsz bt stg le fe xs ws jhb ovd dcb dce trace,
    dctx_ptrs bsegs m DCTX llt mlt oft huf /\ dctx_h1 bsegs m DCTX pde pfx vst dend expd /\ dctx_fp bsegs m DCTX fp /\
    dctx_h3 bsegs m DCTX pcs dsz bt stg le fe /\ dctx_xs bsegs m DCTX xs /\ dctx_h5 bsegs m DCTX ws /\ h5_frame_ok ws /\
    dctx_tx bsegs m DCTX jhb ovd dcb dce trace /\ dctx_owned bsegs m DCTX.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section StmtsF.
Variable AI : AMallocIface.
Variable fflag : alayout -> Z -> Z -> Z.
Variable rng_fs : alayout -> footprint -> Prop.
Definition zd_decodefh_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV DCTX : Z) (src : list Z) (off hsz : Z) (pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' fp' pcs' xs' ws',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (decode_frame_header src off hsz)) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(DCTX + 29928, DCTX + 29984); (DCTX + 30008, DCTX + 30116); (SPV - DECODEFH_STACK_A, SPV)] ++ fake_area L) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [(DCTX + 29928, DCTX + 29984); (DCTX + 30008, DCTX + 30116)] LB m m' /\ AHEAP AI L RNG st LB m'
    /\ dctx_fp bsegs m' DCTX fp' /\ dctx_h3 bsegs m' DCTX pcs' dsz bt stg le fe
    /\ dctx_xs bsegs m' DCTX xs' /\ dctx_h5 bsegs m' DCTX ws'
    /\ match get_frame_header src off hsz with
       | FH_ok h => fp' = zfh_cells h
                    /\ pcs' = Z_to_bv 64 (bv_unsigned pcs + hsz)
                    /\ ws' = wupd ws H5_validateChecksum (Z_to_bv 64 (if fh_checksum h =? 0 then 0 else 1))
                    /\ (if fh_checksum h =? 0 then xs' = xs else exists j1 j2, xs' = xxh_cells j1 0 j2)
       | FH_ret _ => pcs' = pcs /\ xs' = xs /\ ws' = ws
       end.

Definition zd_decodefh_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV DCTX SRC : Z) (src : list Z) (off hsz : Z)
         (fp : list cell) (pcs dsz bt stg le fe : word) (xs : list cell) (ws : list word) (lo : Z),
  dctx_fp bsegs m DCTX fp -> dctx_h3 bsegs m DCTX pcs dsz bt stg le fe -> dctx_xs bsegs m DCTX xs ->
  dctx_h5 bsegs m DCTX ws -> h5_frame_ok ws ->
  4096 <= DCTX -> DCTX + 95992 < 2^47 ->
  bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= off -> 5 <= hsz -> off + hsz <= zlen src -> 0 < SRC ->
  stk bsegs m lo SPV -> lo <= SPV - DECODEFH_STACK_A -> 0 <= SPV < 2^64 ->
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC) ->
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV DECODEFH_DEPTH -> tp = Z_to_bv 64 ATP ->
  aro_client RNG m ->
  areg RNG m SRC (zlen src) -> (0 < zlen src -> ainimg LB SRC (zlen src)) -> DCTX mod 8 = 0 -> areg RNG m DCTX 95992 -> ahull RNG m DCTX 95992 -> ainblk LB DCTX 95992 ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 (SRC + off) -> a2 = Z_to_bv 64 hsz ->
  evtF bsegs RNG (zd_decodefh_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX src off hsz pcs dsz bt stg le fe xs ws lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_DECODEFH) fc None m (seg_rom bsegs)).

Definition zd_dmf_postA (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock) (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SPV DCTX DST CAP : Z) (src : list Z) (size lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' r,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch ([(DCTX, DCTX + 95992); (DST, DST + CAP); (SPV - DMF_STACK_A, SPV)] ++ fake_area L) m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SPV
    /\ ffr_pres [(DCTX, DCTX + 95992); (DST, DST + CAP)] LB m m' /\ AHEAP AI L RNG st LB m'
    /\ dctx_any m' DCTX
    /\ stk bsegs m' DST (DST + CAP)
    /\ 0 <= r < 2^64 /\ (zd_is_error r = false -> decompress_ok src size CAP r).

Definition zd_dmf_stmtA : Prop :=
  forall (L : alayout) (RNG : footprint) (st : astate) (LB : list ablock)
         (ra gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo DCTX DST CAP SRC : Z) (src : list Z) (size : Z),
  dctx_any m DCTX -> 4096 <= DCTX -> DCTX + 95992 < 2^47 -> DCTX mod 8 = 0 ->
  rw_cells bsegs m APZD_GOT_TRACE [C8 wz0; C8 wz0] ->
  bytes_at bsegs m SRC (map (Z_to_bv 8) src) -> all_bytes src -> 0 <= size -> size <= zlen src -> size < 2^40 ->
  4096 <= SRC -> SRC + zlen src < 2^47 ->
  stk bsegs m DST (DST + CAP) -> 0 <= CAP -> CAP < 2^40 -> (DST = 0 -> CAP = 0) -> (DST <> 0 -> 4096 <= DST) -> (CAP = 0 -> DST = 0) -> DST + CAP < 2^47 ->
  stk bsegs m lo SPV -> 4096 <= lo -> lo <= SPV - DMF_STACK_A -> SPV < 2^47 ->
  (DCTX + 95992 <= lo \/ SPV <= DCTX) -> (DST + CAP <= lo \/ SPV <= DST) -> (SRC + zlen src <= lo \/ SPV <= SRC) ->
  (APZD_GOT_TRACE + 16 <= lo \/ SPV <= APZD_GOT_TRACE) ->
  (DST + CAP <= DCTX \/ DCTX + 95992 <= DST) -> (DST + CAP <= SRC \/ SRC + zlen src <= DST) ->
  (SRC + zlen src <= DCTX \/ DCTX + 95992 <= SRC) ->
  (APZD_GOT_TRACE + 16 <= DCTX \/ DCTX + 95992 <= APZD_GOT_TRACE) -> (APZD_GOT_TRACE + 16 <= DST \/ DST + CAP <= APZD_GOT_TRACE) ->
  (* [comment removed for export] *)
  afpre AI rng_fs L RNG st LB m lo SPV DMF_DEPTH -> tp = Z_to_bv 64 ATP ->
  azstk RNG m lo SPV ->
  aro_client RNG m ->
  areg RNG m SRC (zlen src) -> (0 < zlen src -> ainimg LB SRC (zlen src)) -> (0 < zlen src -> ahull RNG m SRC (zlen src)) -> DCTX mod 8 = 0 -> areg RNG m DCTX 95992 -> ahull RNG m DCTX 95992 -> ainblk LB DCTX 95992 ->
  (0 < CAP -> areg RNG m DST CAP /\ ahull RNG m DST CAP /\ ainblk LB DST CAP) ->
  mem_inv bsegs m ->
  a0 = Z_to_bv 64 DCTX -> a1 = Z_to_bv 64 DST -> a2 = Z_to_bv 64 CAP -> a3 = Z_to_bv 64 SRC -> a4 = Z_to_bv 64 size ->
  a5 = wz0 -> a6 = wz0 -> a7 = wz0 ->
  evtF bsegs RNG (zd_dmf_postA L RNG st LB ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DCTX DST CAP src size lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_DMF) fc None m (seg_rom bsegs)).
End StmtsF.
End CANSEC1.
