(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdFrameThm ZdDCtx ZdSeqTable.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Image ZBridge Arr Bytes Frame.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import FseWalkKit MemRange.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.LibA Require Import ExecF Shadow.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.AsanT Require Import BImg ABase AZ_kit AZ_globals AZ_globalsR AZ_huf_iface.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import RunDraw.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition APZD_BITINIT : Z := 0x95b74.     (* [comment removed for export] *)
Definition APZD_INITFSE : Z := 0x96148.     (* [comment removed for export] *)
Definition APZD_RELOADI : Z := 0x967a8.     (* [comment removed for export] *)
Definition SBITMASK : Z := 0x22180.         (* [comment removed for export] *)
Notation INITFSE_STACK_A := 16 (only parsing).
Notation RELOADI_STACK_A := 16 (only parsing).

(* [comment removed for export] *)
Definition sbitmask_bytes : list byte := Eval vm_compute in match image_bytes bsegs SBITMASK 128 with Some bs => bs | None => [] end.
Lemma sbitmask_at : forall m, mem_inv bsegs m -> bytes_at bsegs m SBITMASK sbitmask_bytes.
Proof.
  intros m MI. pose proof (ro_cells_image bsegs m SBITMASK sbitmask_bytes MI ltac:(vm_compute; reflexivity) ltac:(vm_compute; discriminate) ltac:(vm_compute; discriminate)) as [_ H].
  cbn [cells_bytes cbytes] in H. rewrite app_nil_r in H. exact H.
Qed.
Lemma sbytes_eq_unsigned : forall a b : list byte, map (@bv_unsigned 8) a = map (@bv_unsigned 8) b -> a = b.
Proof.
  induction a as [|x a IH]; intros [|y b] H; try discriminate; [reflexivity|].
  cbn [map] in H. injection H as H1 H2. f_equal; [apply bv_eq; exact H1 | apply IH; exact H2].
Qed.
Lemma sbitmask_know : forall m nb, mem_inv bsegs m -> 0 <= nb <= 31 ->
  rdn bsegs m (wa (SBITMASK + 4 * nb)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 (2^nb - 1))).
Proof.
  intros m nb MI H. replace (SBITMASK + 4 * nb) with (SBITMASK + Z.of_nat (Z.to_nat (4 * nb))) by lia.
  rewrite (bytes_at_rdn bsegs m SBITMASK sbitmask_bytes (Z.to_nat (4 * nb)) 4 (sbitmask_at m MI)) by (change (length sbitmask_bytes) with 128%nat; lia).
  f_equal. assert (C : exists k : nat, (k <= 31)%nat /\ nb = Z.of_nat k) by (exists (Z.to_nat nb); lia).
  destruct C as (k & Hk & ->). do 32 (destruct k as [|k]; [apply sbytes_eq_unsigned; vm_compute; reflexivity|]). lia.
Qed.

Lemma sland_mask_lt : forall x nb, 0 <= nb <= 62 -> 0 <= Z.land x ((2^nb + -1) mod 2^64) < 2^nb.
Proof.
  intros x nb Hn. assert (P : 0 < 2^nb) by (apply Z.pow_pos_nonneg; lia).
  assert (Q : 2^nb <= 2^62) by (apply Z.pow_le_mono_r; lia).
  rewrite Z.mod_small by lia. replace (2^nb + -1) with (Z.ones nb) by (rewrite Z.ones_equiv; lia).
  rewrite Z.land_ones by lia. apply Z.mod_pos_bound. exact P.
Qed.

Section CANSEC1. Context {rc : runConstT}.
(* [comment removed for export] *)
Definition bit_okS (SEQ n bc ptr : Z) : Prop := bc <= 64 -> ptr = SEQ \/ (8 <= n /\ SEQ <= ptr <= SEQ + n - 8).
Definition sbd_cells (cw : word) (bc : Z) (jpad : list byte) (ptr SEQ : Z) : list cell :=
  [C8 cw; C4 (Z_to_bv 64 bc); CB 4 jpad; C8 (Z_to_bv 64 ptr); C8 (Z_to_bv 64 SEQ); C8 (Z_to_bv 64 (SEQ + 8))].

(* [comment removed for export] *)
Definition zd_reload_int_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV BD SEQ bc ptr lo : Z) (jpad : list byte) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' cw',
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(BD, BD + 40); (SPV - RELOADI_STACK_A, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
    /\ rw_cells bsegs m' BD (sbd_cells cw' (bc mod 8) jpad (ptr - bc / 8) SEQ).

Definition zd_reload_int_stmtA : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo BD SEQ bc ptr : Z) (cw : word) (jpad sqb : list byte),
  rw_cells bsegs m BD (sbd_cells cw bc jpad ptr SEQ) -> bytes_at bsegs m SEQ sqb ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SEQ -> SEQ + Z.of_nat (length sqb) < 2^47 -> BD mod 8 = 0 ->
  (BD + 40 <= SEQ \/ SEQ + Z.of_nat (length sqb) <= BD) ->
  0 <= bc <= 64 -> SEQ + 8 <= ptr -> ptr <= SEQ + Z.of_nat (length sqb) - 8 ->
  stk bsegs m lo SPV -> lo <= SPV - RELOADI_STACK_A -> SPV < 2^47 ->
  (BD + 40 <= lo \/ SPV <= BD) -> (SEQ + Z.of_nat (length sqb) <= lo \/ SPV <= SEQ) ->
  (* [comment removed for export] *)
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> aro RNG m SEQ (Z.of_nat (length sqb)) -> art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  evtF bsegs RNG (zd_reload_int_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BD SEQ bc ptr lo jpad m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_RELOADI) fc None m (seg_rom bsegs)).

(* [comment removed for export] *)
Definition zd_initfse_postA (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (SPV BD STP T SEQ n B tl lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' cw' bc' jpad' ptr' st,
    ms' = MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch [(BD, BD + 40); (STP, STP + 16); (SPV - INITFSE_STACK_A, SPV)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo SPV
    /\ rw_cells bsegs m' BD (sbd_cells cw' bc' jpad' ptr' SEQ)
    /\ rw_cells bsegs m' STP [C8 (Z_to_bv 64 st); C8 (Z_to_bv 64 (T + 8))]
    /\ 0 <= st < 2^tl /\ 0 <= bc' <= B + 9 /\ bit_okS SEQ n bc' ptr'.

(* [comment removed for export] *)
Definition zd_initfse_stmtA_if (CND : Z -> Z -> Z -> Z -> Z -> Prop) : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV lo BD STP T SEQ B bc ptr : Z) (cw st0 tb0 : word) (jpad sqb : list byte)
         (k : seq_kind) (t : seq_table),
  rw_cells bsegs m BD (sbd_cells cw bc jpad ptr SEQ) -> rw_cells bsegs m STP [C8 st0; C8 tb0] ->
  bytes_at bsegs m T (map (Z_to_bv 8) (seq_table_bytes t)) -> seq_table_ok k t ->
  bytes_at bsegs m SEQ sqb ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= STP -> STP + 16 < 2^47 -> 4096 <= T -> T + 8 * (1 + 2^(st_log t)) < 2^47 ->
  4096 <= SEQ -> SEQ + Z.of_nat (length sqb) < 2^47 -> 1 <= Z.of_nat (length sqb) ->
  BD mod 8 = 0 -> STP mod 8 = 0 -> T mod 4 = 0 ->
  (BD + 40 <= STP \/ STP + 16 <= BD) -> (BD + 40 <= SEQ \/ SEQ + Z.of_nat (length sqb) <= BD) -> (STP + 16 <= SEQ \/ SEQ + Z.of_nat (length sqb) <= STP) ->
  (BD + 40 <= T \/ T + 8 * (1 + 2^(st_log t)) <= BD) -> (STP + 16 <= T \/ T + 8 * (1 + 2^(st_log t)) <= STP) ->
  0 <= bc <= B -> B <= 82 -> bit_okS SEQ (Z.of_nat (length sqb)) bc ptr ->
  stk bsegs m lo SPV -> lo <= SPV - INITFSE_STACK_A -> SPV < 2^47 ->
  (BD + 40 <= lo \/ SPV <= BD) -> (STP + 16 <= lo \/ SPV <= STP) ->      (* [comment removed for export] *)
  (SEQ + Z.of_nat (length sqb) <= lo \/ SPV <= SEQ) -> (T + 8 * (1 + 2^(st_log t)) <= lo \/ SPV <= T) ->
  (* [comment removed for export] *)
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> app_blk STP (STP + 16) -> aro RNG m STP 16 ->
  aro RNG m SEQ (Z.of_nat (length sqb)) -> aro RNG m T (8 * (1 + 2^(st_log t))) -> aro_client RNG m ->
  art m -> astk RNG lo SPV ->
  mem_inv bsegs m ->
  CND bc (st_log t) ptr SEQ (Z.of_nat (length sqb)) ->
  evtF bsegs RNG (zd_initfse_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BD STP T SEQ (Z.of_nat (length sqb)) B (st_log t) lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 STP) (Z_to_bv 64 BD) (Z_to_bv 64 T) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 APZD_INITFSE) fc None m (seg_rom bsegs)).
Definition zd_initfse_stmtA : Prop := zd_initfse_stmtA_if (fun _ _ _ _ _ => True).
(* [comment removed for export] *)
Definition bit_init_stmtS_at (ENTRY : Z) : Prop :=
  forall (RNG : footprint) (ra gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (SPV BD SRC n lo : Z) (src junk : list byte),
  mem_inv bsegs m ->
  rw_cells bsegs m BD [CB 40 junk] -> BD mod 8 = 0 ->      (* [comment removed for export] *)
  bytes_at bsegs m SRC src -> zlen src = n ->
  4096 <= BD -> BD + 40 < 2^47 -> 4096 <= SRC -> SRC + n < 2^47 ->
  (BD + 40 <= SRC \/ SRC + n <= BD) ->
  stk bsegs m lo SPV -> lo <= SPV - BITINIT_STACK_A -> SPV < 2^47 ->
  (BD + 40 <= lo \/ SPV <= BD) -> (SRC + n <= lo \/ SPV <= SRC) ->
  (* [comment removed for export] *)
  app_blk BD (BD + 40) -> aro RNG m BD 40 -> ahull RNG m BD 40 -> aro RNG m SRC n ->
  art m -> astk RNG lo SPV ->
  evtF bsegs RNG (bit_init_postA ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV BD SRC n lo m)
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 BD) (Z_to_bv 64 SRC) (Z_to_bv 64 n) a3 a4 a5 a6 a7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom bsegs)).


End CANSEC1.
