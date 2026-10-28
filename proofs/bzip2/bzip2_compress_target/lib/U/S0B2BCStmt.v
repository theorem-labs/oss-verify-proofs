(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.bzip2.bzip2_compress_target.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec ShapeAlg.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import MState Mem Cells Step Frame Image. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocIface. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Heap Require Import AllocLayout0. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Heap Require Import AllocCover.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzIncs. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCDriver. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpMem. From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCut0 BzRT1.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)

Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil} {RUNW__ : RunW}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record B2BCImg := BCI {
  bc_ci       : cimg;   (* [comment removed for export] *)
  bc_entry    : Z;      (* [comment removed for export] *)
  bc_init     : Z;      (* [comment removed for export] *)
  bc_end      : Z;      (* [comment removed for export] *)
  bc_dbzalloc : Z;      (* [comment removed for export] *)
  bc_dbzfree  : Z;      (* [comment removed for export] *)
  bc_malloc   : Z;      (* [comment removed for export] *)
  bc_free     : Z
}.
Definition S0CI : B2BCImg := BCI S0C 0x15e1c 0x13c04 0x14528 0x13e24 0x13e3c 0x29504 0x293c4.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition b2bC_mem (I : B2BCImg) (m : word -> option byte) (sv : word) : Prop := cimg_mem (bc_ci I) m sv.

(* [comment removed for export] *)
Definition B2BC_STACK : Z := 17408.

(* [comment removed for export] *)
Definition BZ_OK_ : Z := 0.
Definition BZ_PARAM_ERROR_ : Z := -2.
Definition BZ_MEM_ERROR_ : Z := -3.
Definition BZ_OUTBUFF_FULL_ : Z := -8.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stmt.
  Variable segs : list Segment.
  Variable L : alloc_layout.
  Variable AI : AllocIface segs L.
  Variable AC : AllocCover segs L AI.   (* [comment removed for export] *)
  Variable I : B2BCImg.

  (* [comment removed for export] *)
  Definition b2bC_out (dst nZ dl : Z) (a : Z) : Prop := (dst <> 0 /\ dst <= a < dst + nZ) \/ (dl <= a < dl + 4).
  (* [comment removed for export] *)
  Definition b2bC_pres (LB : list ablock) (SP : Z) (dst nZ dl : Z) (m m' : word -> option byte) : Prop :=
    forall a : Z, 0 <= a < 2 ^ 64 -> client_addr L LB SP a -> ~ b2bC_out dst nZ dl a ->
      m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

  (* [comment removed for export] *)
  Definition b2bC_result (rc : Z) (dst nZ : Z) (payload junk : list byte) (m' : word -> option byte) (dlv : Z) : Prop :=
    (rc = BZ_PARAM_ERROR_ /\ dst = 0 /\ dlv = nZ)
    \/ (rc = BZ_MEM_ERROR_ /\ dst <> 0 /\ dlv = nZ /\ rw_cells segs m' dst [CB (Z.to_nat nZ) junk])
    \/ (exists (a1 a2 ft inU uns mtf sel selM len code rfreq lenp : zarr) (bsB bsL nIn oP nM : Z) (junk' : list byte),
          a1 = znew /\ a2 = znew /\ ft = znew /\
          let e0 := est_init a1 a2 ft inU uns mtf sel selM len code rfreq lenp bsB bsL nIn oP nM in
          let str := enc_stream e0 (map bv_unsigned payload) in
          dst <> 0 /\
          (   (rc = BZ_OK_ /\ Z.of_nat (length str) <= nZ /\ dlv = Z.of_nat (length str)
               /\ rw_cells segs m' dst [CB (length str) (map (Z_to_bv 8) str); CB (Z.to_nat (nZ - Z.of_nat (length str))) junk'])
           \/ (rc = BZ_OUTBUFF_FULL_ /\ nZ < Z.of_nat (length str) /\ dlv = nZ
               /\ rw_cells segs m' dst [CB (Z.to_nat nZ) junk']))).

  (* [comment removed for export] *)
  Definition b2bC_post
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list ablock) (m : word -> option byte) (MD : Model)
      (dst nZ dl lo B : Z) (payload junk : list byte) (sv : word) (k : nat)
      (ms' : machine_state) (MD' : Model) : Prop :=
    exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 errv' : word) (m' : word -> option byte)
           (s' : ai_AS AI) (rc dlv : Z),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc ra) fc None m' (seg_rom segs)
      /\ a0 = Z_to_bv 64 rc
      (* [comment removed for export] *)
      /\ ai_inv AI s' LB m' MD' /\ ac_vm AC k s' MD'
      /\ vm_only MD MD'
      /\ mem_inv segs m'
      /\ stk segs m' lo (bv_unsigned sp)
      /\ rw_cells segs m' (errno_cell L) [C4 errv']
      /\ ai_aux AI m' B
      (* [comment removed for export] *)
      /\ b2bC_pres LB (bv_unsigned sp) dst nZ dl m m'
      (* [comment removed for export] *)
      /\ rw_cells segs m' dl [C4 (Z_to_bv 64 dlv)] /\ 0 <= dlv <= nZ
      (* [comment removed for export] *)
      /\ b2bC_mem I m' sv
      (* [comment removed for export] *)
      /\ b2bC_result rc dst nZ payload junk m' dlv.

  (* [comment removed for export] *)
  Definition b2bC_spec : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
           (s : ai_AS AI) (LB : list ablock) (p : bid)
           (dst nZ dl src len wf0 lo B : Z) (payload junk : list byte) (errv sv : word) (k : nat)
           (K : TSet),
      (* [comment removed for export] *)
      a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 dl -> a2 = Z_to_bv 64 src -> a3 = Z_to_bv 64 len ->
      a4 = Z_to_bv 64 BLOCKSIZE100K -> a5 = Z_to_bv 64 0 -> a6 = Z_to_bv 64 wf0 ->
      0 <= wf0 <= 250 -> WORKFACTOR = (if wf0 =? 0 then 30 else wf0) ->
      tp = Z_to_bv 64 (al_tp L) ->
      0 <= len < 2 ^ 26 -> nZ = len + 600 + len / 100 ->
      (* [comment removed for export] *)
      ai_inv AI s LB m MD -> ac_vm AC (4 + k)%nat s MD ->
      ai_aux AI m B -> bv_unsigned sp <= B ->
      (* [comment removed for export] *)
      (dst = 0 \/ (In (p, dst, nZ) LB /\ rw_cells segs m dst [CB (Z.to_nat nZ) junk])) ->
      (* [comment removed for export] *)
      rw_cells segs m dl [C4 (Z_to_bv 64 nZ)] ->
      bv_unsigned sp <= dl -> dl + 4 <= 2 ^ 64 -> dl mod 4 = 0 ->   (* [comment removed for export] *)
      dl + 4 <= B ->
      (* [comment removed for export] *)
      bytes_at segs m src payload -> Z.of_nat (length payload) = len ->
      client_range L LB (bv_unsigned sp) src len -> 0 < src -> src + len <= alloc_ceiling -> src mod 16 = 0 ->   (* [comment removed for export] *)
      (len = 0 \/ exists b, In b LB /\ blk_addr b <= src /\ src + len <= blk_addr b + blk_size b) ->
      (dst <> 0 -> src + len <= dst \/ dst + nZ <= src) -> (src + len <= dl \/ dl + 4 <= src) ->
      (dst <> 0 -> dst + nZ <= dl \/ dl + 4 <= dst) ->
      (* [comment removed for export] *)
      stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - B2BC_STACK ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 48 <= 2 ^ 47 ->
      (* [comment removed for export] *)
      rw_cells segs m (errno_cell L) [C4 errv] ->
      mem_inv segs m ->
      b2bC_mem I m sv ->
      (* [comment removed for export] *)
      (forall ms' MD',
         b2bC_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB m MD dst nZ dl lo B payload junk sv k ms' MD' ->
         realizes segs (mkCfg ms' MD') K) ->
      realizes segs
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (bc_entry I)) fc None m (seg_rom segs)) MD)
        K.
End Stmt.
End ACeilS1.

Arguments b2bC_spec {BZP ACEIL__ segs L} AI AC I.
Arguments b2bC_post {BZP ACEIL__ segs L} AI AC I.
Arguments b2bC_result {BZP} segs.

Section ACeilS2. Context {BZP : BzParams} {ACEIL__ : ACeil} {RUNW__ : RunW}.
(* [comment removed for export] *)
(* [comment removed for export] *)
End ACeilS2.
