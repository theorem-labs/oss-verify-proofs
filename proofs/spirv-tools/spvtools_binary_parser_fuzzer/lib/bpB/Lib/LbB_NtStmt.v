(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_MILB LbB_PrsStmt LbB_Own LbB_ContStmt LbB_HEmpStmt.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition NT_ENTRY  : Z := 0xf5128.
Definition NT_EXIT   : Z := 0xf5d28.
Definition NT_DEL_RA : Z := 0xf5618.

Definition ANT_STACK : Z := AOPNEW_STACK.

Definition lo32 (w : word) : Z := bv_unsigned w mod 2 ^ 32.

Section Stmts.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

  Definition nt_slots (m : mem) (S1 obj v408 v576 v624 : Z) : Prop :=
    rw_cells asegs m (S1 + 408) [C8 (Z_to_bv 64 v408)]
    /\ rw_cells asegs m (S1 + 576) [C8 (Z_to_bv 64 v576)]
    /\ rw_cells asegs m (S1 + 616) [C8 (Z_to_bv 64 SHBASE)]
    /\ rw_cells asegs m (S1 + 624) [C8 (Z_to_bv 64 v624)]
    /\ rw_cells asegs m (S1 + 648) [C8 (Z_to_bv 64 (obj - 136))].

  Definition nt_wslots (m : mem) (S1 obj : Z) (ty enc : word) : Prop :=
    rw_cells asegs m (S1 + 600) [C8 enc; C8 ty]
    /\ rw_cells asegs m (S1 + 632) [C8 (Z_to_bv 64 (obj + 8)); C8 (Z_to_bv 64 (obj / 8))]
    /\ rw_cells asegs m (S1 + 656) [C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 (sh (obj + 8)))].

  Definition nt_X (S1 obj : Z) : list (Z * Z) :=
    [(obj, obj + 40); (S1 + 584, S1 + 616); (S1 + 632, S1 + 648); (S1 + 656, S1 + 672)].

  Definition nt_post (gp tp s0 s4 : word)
      (s : as_St H) (LB0 : list block) (LF : list fframe) (S1 obj key v408 v576 v624 : Z) (val : Z * Z * Z)
      (ents : list ent) (bl bc lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists ra' t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2' s5' s6' s8' s9' t3 t4 t5 t6 m' (errv' : word) (s' : as_St H)
                     (LB' LBm' : list block) (F' : bvmap 5 word) (fc' : bv 32) (p bl' bc' : Z) (ents' : list ent)
                     (inserted rehashed : bool) (j584 j592 j600 j608 j632 j640 j656 j664 : word),
      as_VIS H s' (cfg_ms cf) = MS (mkR ra' (Z_to_bv 64 S1) gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7
                                        s2' (Z_to_bv 64 v624) s4 s5' s6' (Z_to_bv 64 (obj - 136)) s8' s9'
                                        (Z_to_bv 64 v408) (Z_to_bv 64 v576) t3 t4 t5 t6)
                                   F' (Z_to_bv 64 NT_EXIT) fc' None m' (seg_rom asegs)
      /\ frm_zero fc'
      /\ as_AKREL H s' cf /\ as_MPRES H mo (cfg_model cf)
      /\ mem_inv asegs m' /\ stk asegs m' lo (S1 + 672)
      /\ rw_cells asegs m' (errno_addr tp) [C4 errv'] /\ as_rauxv_ok H m' B

      /\ umapx MI_A 32 (nval32 ASEGS) (lbl LB') m' obj bl' bc' ents' /\ umap_sh m' 32 (bl', bc', ents')
      /\ addressable m' obj 40 /\ wr_at asegs m' obj 40
      /\ In (p, (key, val)) ents'
      /\ (inserted = false -> exists v0 l1 l2, ents = l1 ++ (p, (key, v0)) :: l2 /\ ents' = l1 ++ (p, (key, val)) :: l2
                             /\ rehashed = false)
      /\ (inserted = true -> Permutation ents' ((p, (key, val)) :: ents))
      /\ (rehashed = false -> bl' = bl /\ bc' = bc)
      /\ (rehashed = true -> (bc = 0 \/ Zlength ents = bc) /\ bc' = bseq_next bc)

      /\ as_RHEAP H s' LB' m' /\ Permutation LB' (LB0 ++ LBm') /\ Permutation (lbl LBm') (umap_blocks 32 bl' bc' ents')
      /\ lb_own LBm' m'
      /\ xpres H LB0 S1 (nt_X S1 obj) m m'

      /\ rw_cells asegs m' (S1 + 584) [C8 j584; C8 j592; C8 j600; C8 j608]
      /\ rw_cells asegs m' (S1 + 632) [C8 j632; C8 j640] /\ rw_cells asegs m' (S1 + 656) [C8 j656; C8 j664]
      /\ as_RFS H LF m' /\ ACONST m' /\ stack0 m' lo shi
      /\ as_AL H s' >= as_AL H s - (if rehashed then ICM (8 * bc') else 0).

  Definition nt_stmt : Prop :=
    forall (ra gp tp t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s6 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe) (CH : list (Z * Z))
           (S1 obj bl bc keyp key v408 v576 v624 : Z) (ents : list ent) (lo B shi : Z)
           (errv j584 j592 j600 j608 j632 j640 j656 j664 : word),
      as_VIS H s msF = MS (mkR ra (Z_to_bv 64 S1) gp tp t0 t1 t2 s0 (Z_to_bv 64 S1) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4
                              (Z_to_bv 64 keyp) s6 (Z_to_bv 64 (obj - 136)) s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 NT_ENTRY) fc None m (seg_rom asegs) ->
      frm_zero fc ->

      umapx MI_A 32 (nval32 ASEGS) (lbl LB) m obj bl bc ents -> umap_sh m 32 (bl, bc, ents) ->
      Permutation LB (LB0 ++ LBm) -> Permutation (lbl LBm) (umap_blocks 32 bl bc ents) ->
      addressable m obj 40 -> wr_at asegs m obj 40 -> map_live_frame LF obj -> obj + 40 <= aceil ->
      (forall b, In b LB -> obj + 40 <= blk_addr b \/ blk_addr b + blk_size b <= obj) ->

      fldA m keyp 4 key -> emp_src H LB0 S1 obj keyp 4 -> 0 <= keyp -> keyp + 4 <= aceil -> keyp mod 4 = 0 -> 0 <= key < 2 ^ 32 ->

      nt_slots m S1 obj v408 v576 v624 -> 0 <= v408 < 2 ^ 64 -> 0 <= v576 < 2 ^ 64 -> 0 <= v624 < 2 ^ 64 ->
      rw_cells asegs m (S1 + 584) [C8 j584; C8 j592; C8 j600; C8 j608] ->
      rw_cells asegs m (S1 + 632) [C8 j632; C8 j640] -> rw_cells asegs m (S1 + 656) [C8 j656; C8 j664] ->

      Zlength ents + 1 < 2 ^ 24 -> bc <> BSEQ_LAST ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
      lb_small LB + 32 + nsmall (8 * bseq_next bc) <= RT_SMALL_MAX -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX ->
      nlarge LB + nlg (8 * bseq_next bc) <= RT_LARGE_MAX ->
      ((bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s) ->

      as_chain H m (bv_unsigned s0) CH -> trace_ok (as_TR H) APC0_FREE (NT_DEL_RA :: map snd CH) ->
      (forall fp' ra', In (fp', ra') CH -> S1 + 688 <= fp') ->
      as_rauxv_ok H m B -> S1 + 672 <= B -> B < 2^64 ->

      S1 mod 16 = 0 ->
      stk asegs m lo (S1 + 672) -> aceil <= lo -> lo <= S1 - ANT_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      ACONST m -> as_RFS H LF m -> stack0 m lo shi -> S1 + 672 <= shi ->
      lb_own LBm m ->
      as_SR H (nt_post gp tp s0 s4 s LB0 LF S1 obj key v408 v576 v624 (lo32 s10, lo32 s8, lo32 a5) ents bl bc lo B shi m mo)
              (mkCfg msF mo).
End Stmts.
