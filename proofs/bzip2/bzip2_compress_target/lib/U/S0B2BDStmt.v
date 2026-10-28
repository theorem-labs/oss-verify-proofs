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
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzArr BzDState BzDOut.
From Stdlib Require Lia. Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil RunW.

Section ACeilS1. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record B2BDImg := BDI {
  bd_entry   : Z;      (* [comment removed for export] *)
  bd_crc     : Z;      (* [comment removed for export] *)
  bd_rnums   : Z;      (* [comment removed for export] *)
  bd_got     : Z;      (* [comment removed for export] *)
  bd_stderrp : Z       (* [comment removed for export] *)
}.
Definition S0DI : B2BDImg := BDI 0x15f2c 0x33178 0x335b0 0x320e8 0x32098.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition b2bD_got (segs : list Segment) (I : B2BDImg) (m : word -> option byte) (g1 sv : word) : Prop :=
  rw_cells segs m (bd_got I) [C8 (Z_to_bv 64 (bd_stderrp I)); C8 g1; C8 (Z_to_bv 64 (bd_stderrp I + 8)); C8 (Z_to_bv 64 (bd_crc I)); C8 (Z_to_bv 64 (bd_rnums I))]
  /\ rw_cells segs m (bd_stderrp I) [C8 sv].

(* [comment removed for export] *)
Definition b2bD_tabs (segs : list Segment) (I : B2BDImg) (m : word -> option byte) : Prop :=
  rw_cells segs m (bd_crc I) [CB 1024 bz_crc_table_bytes] /\ rw_cells segs m (bd_rnums I) [CB 2048 bz_rnums_table_bytes].

(* [comment removed for export] *)
Definition B2BD_STACK : Z := 16384.

(* [comment removed for export] *)
Definition BZD_PARAM_ERROR : Z := -2.
Definition BZD_MEM_ERROR : Z := -3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Stmt.
  Variable segs : list Segment.
  Variable L : alloc_layout.
  Variable AI : AllocIface segs L.
  Variable AC : AllocCover segs L AI.
  Variable I : B2BDImg.

  (* [comment removed for export] *)
  Definition b2bD_out (dst dn dl : Z) (a : Z) : Prop := (dst <> 0 /\ dst <= a < dst + dn) \/ (dl <= a < dl + 4).
  (* [comment removed for export] *)
  Definition b2bD_pres (LB : list ablock) (SP : Z) (dst dn dl : Z) (m m' : word -> option byte) : Prop :=
    forall a : Z, 0 <= a < 2 ^ 64 -> client_addr L LB SP a -> ~ b2bD_out dst dn dl a ->
      m' (wa a) = m (wa a) /\ (wview segs m (wa a) <> None -> wview segs m' (wa a) <> None).

  (* [comment removed for export] *)
  Definition b2bD_result (rc : Z) (dst dn : Z) (srcZ : list Z) (small : Z) (m' : word -> option byte) (dlv : Z) : Prop :=
    (rc = BZD_PARAM_ERROR /\ dst = 0 /\ dlv = dn)
    \/ (rc = BZD_MEM_ERROR /\ dst <> 0 /\ dlv = dn /\ exists junk', rw_cells segs m' dst [CB (Z.to_nat dn) junk'])
    \/ (dst <> 0 /\ exists (junkD : BzDState.dst) (junk' : list byte),
          let '(r, n, out, _) := buffToBuffDecompress junkD srcZ dn small in
          rc = r
          /\ (r = BZ_OK -> dlv = n /\ Z.of_nat (length out) = n /\
                rw_cells segs m' dst [CB (length out) (map (Z_to_bv 8) out); CB (Z.to_nat (dn - n)) junk'])
          /\ (r <> BZ_OK -> rw_cells segs m' dst [CB (Z.to_nat dn) junk'])).

  (* [comment removed for export] *)
  Definition b2bD_post
      (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (LB : list ablock) (m : word -> option byte) (MD : Model)
      (dst dn dl : Z) (srcZ : list Z) (small lo B : Z) (g1 sv : word) (k : nat)
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
      /\ b2bD_pres LB (bv_unsigned sp) dst dn dl m m'
      (* [comment removed for export] *)
      /\ rw_cells segs m' dl [C4 (Z_to_bv 64 dlv)] /\ 0 <= dlv <= dn
      (* [comment removed for export] *)
      /\ b2bD_tabs segs I m' /\ b2bD_got segs I m' g1 sv
      (* [comment removed for export] *)
      /\ b2bD_result rc dst dn srcZ small m' dlv.

  (* [comment removed for export] *)
  Definition b2bD_spec : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (MD : Model)
           (s : ai_AS AI) (LB : list ablock) (p : bid)
           (dst dn dl src slen small lo B : Z) (srcb junk : list byte) (errv g1 sv : word) (k : nat)
           (K : TSet),
      (* [comment removed for export] *)
      a0 = Z_to_bv 64 dst -> a1 = Z_to_bv 64 dl -> a2 = Z_to_bv 64 src -> a3 = Z_to_bv 64 slen ->
      a4 = Z_to_bv 64 small -> a5 = Z_to_bv 64 0 ->
      tp = Z_to_bv 64 (al_tp L) ->
      0 <= slen < 2 ^ 27 -> 0 <= dn < 2 ^ 27 -> (small = 0 \/ small = 1) ->
      (* [comment removed for export] *)
      ai_inv AI s LB m MD -> ac_vm AC (3 + k)%nat s MD ->
      ai_aux AI m B -> bv_unsigned sp <= B ->
      (* [comment removed for export] *)
      (dst = 0 \/ (In (p, dst, dn) LB /\ rw_cells segs m dst [CB (Z.to_nat dn) junk])) ->
      (* [comment removed for export] *)
      rw_cells segs m dl [C4 (Z_to_bv 64 dn)] ->
      bv_unsigned sp <= dl -> dl + 4 <= 2 ^ 64 -> dl mod 4 = 0 ->   (* [comment removed for export] *)
      dl + 4 <= B ->
      (* [comment removed for export] *)
      bytes_at segs m src srcb -> Z.of_nat (length srcb) = slen ->
      client_range L LB (bv_unsigned sp) src slen -> 0 < src -> src + slen <= alloc_ceiling -> src mod 16 = 0 ->
      (dst <> 0 -> src + slen <= dst \/ dst + dn <= src) -> (src + slen <= dl \/ dl + 4 <= src) ->
      (dst <> 0 -> dst + dn <= dl \/ dl + 4 <= dst) ->
      (* [comment removed for export] *)
      stk segs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - B2BD_STACK ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 48 <= 2 ^ 47 ->
      (* [comment removed for export] *)
      rw_cells segs m (errno_cell L) [C4 errv] ->
      mem_inv segs m ->
      b2bD_tabs segs I m -> b2bD_got segs I m g1 sv ->
      (* [comment removed for export] *)
      (forall ms' MD',
         b2bD_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc LB m MD dst dn dl (map bv_unsigned srcb) small lo B g1 sv k ms' MD' ->
         realizes segs (mkCfg ms' MD') K) ->
      realizes segs
        (mkCfg (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 (bd_entry I)) fc None m (seg_rom segs)) MD)
        K.
End Stmt.
End ACeilS1.

Arguments b2bD_spec {ACEIL__ segs L} AI AC I.
Arguments b2bD_post {ACEIL__ segs L} AI AC I.

Section ACeilS2. Context {ACEIL__ : ACeil} {RUNW__ : RunW}.
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
(* [comment removed for export] *)   (* [comment removed for export] *)
End ACeilS2.
