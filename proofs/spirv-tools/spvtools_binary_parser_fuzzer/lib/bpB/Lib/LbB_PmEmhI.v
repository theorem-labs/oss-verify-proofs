(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_ContStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwImg LbB_RwKit LbB_RwSem LbB_RwStm.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_Own LbB_HEmpStmt LbB_DStat.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_PmEmhW.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_PmEmh.

Section EmhI.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition emh_SB (I : emh_inst) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe) (obj bl bc keyp key : Z) (ents : list (Z * (Z * Z)))
      (lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists t0 t1 t2 a2 a4 a5 a6 a7 t3 t4 t5 t6 (m1 : mem) (errv1 : word) (ff fp : Z),
      as_VIS H s (cfg_ms cf) = MS (mkR (Z_to_bv 64 (emh_entry I + 296)) (Z_to_bv 64 (emh_sq (bv_unsigned sp))) gp tp t0 t1 t2
                                      sp (Z_to_bv 64 (emh_sq (bv_unsigned sp))) (Z_to_bv 64 obj) (Z_to_bv 64 keyp) a2
                                      (Z_to_bv 64 (ff + 32)) a4 a5 a6 a7 (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff)
                                      s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                  F (Z_to_bv 64 (emp_entry (emh_emp I))) fc None m1 (seg_rom asegs)
      /\ frm_zero fc /\ as_AKREL H s cf /\ as_MPRES H mo (cfg_model cf)
      /\ fresh_frame H LF 1 ff fp /\ as_RFS H ((1, ff, fp) :: LF) m1
      /\ umapx MI_A 24 (nval24 ASEGS) (lbl LB) m1 obj bl bc ents /\ umap_sh m1 24 (bl, bc, ents)
      /\ addressable m1 obj 40 /\ wr_at asegs m1 obj 40
      /\ fldA m1 keyp 4 key /\ accessible m1 keyp 4 /\ fldA m1 (ff + 32) 8 keyp /\ accessible m1 (ff + 32) 8
      /\ as_RHEAP H s LB m1 /\ lb_own LBm m1 /\ as_rauxv_ok H m1 B
      /\ stk asegs m1 lo (bv_unsigned sp) /\ rw_cells asegs m1 (errno_addr tp) [C4 errv1] /\ mem_inv asegs m1
      /\ ACONST m1 /\ stack0 m1 lo shi
      /\ fldA m1 (bv_unsigned sp - 8) 8 (bv_unsigned ra) /\ fldA m1 (bv_unsigned sp - 16) 8 (bv_unsigned s0)
      /\ fldA m1 (bv_unsigned sp - 24) 8 (bv_unsigned s1) /\ fldA m1 (bv_unsigned sp - 32) 8 (bv_unsigned s2)
      /\ fldA m1 (bv_unsigned sp - 40) 8 (bv_unsigned s3) /\ fldA m1 (bv_unsigned sp - 48) 8 (bv_unsigned s4)
      /\ fldA m1 (ff + 120) 8 fp /\ wr_at asegs m1 fp 1 /\ wr_at asegs m1 ff 128 /\ wr_at asegs m1 (sh ff) 16
      /\ xpres H LB0 (bv_unsigned sp) [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] m m1.

  Definition emh_SC (I : emh_inst) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe) (obj bl bc keyp key : Z) (ents : list (Z * (Z * Z)))
      (lo B shi : Z) (m : mem) (mo : Model) : config -> Prop :=
    fun cf => exists (m1 : mem) (ff fp : Z),
      fresh_frame H LF 1 ff fp /\ stk asegs m1 lo (bv_unsigned sp)
      /\ fldA m1 (bv_unsigned sp - 8) 8 (bv_unsigned ra) /\ fldA m1 (bv_unsigned sp - 16) 8 (bv_unsigned s0)
      /\ fldA m1 (bv_unsigned sp - 24) 8 (bv_unsigned s1) /\ fldA m1 (bv_unsigned sp - 32) 8 (bv_unsigned s2)
      /\ fldA m1 (bv_unsigned sp - 40) 8 (bv_unsigned s3) /\ fldA m1 (bv_unsigned sp - 48) 8 (bv_unsigned s4)
      /\ fldA m1 (ff + 120) 8 fp /\ wr_at asegs m1 fp 1 /\ wr_at asegs m1 ff 128 /\ wr_at asegs m1 (sh ff) 16
      /\ xpres H LB0 (bv_unsigned sp) [(as_FSB H, as_FSB H + AFS_FLAGS); (fp, fp + 1); (ff, ff + fsz 1); (sh ff, sh ff + fshn 1)] m m1
      /\ emp_post H (Z_to_bv 64 (emh_entry I + 296)) (Z_to_bv 64 (emh_sq (bv_unsigned sp))) gp tp sp (Z_to_bv 64 (emh_sq (bv_unsigned sp)))
           (Z_to_bv 64 ff) (Z_to_bv 64 (sh ff)) (Z_to_bv 64 ff) s5 s6 s7 s8 s9 s10 s11 s LB0 ((1, ff, fp) :: LF) obj bl bc key ents lo B shi m1 mo cf.

  Definition emh_toB_stmt (I : emh_inst) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe)
           (obj bl bc keyp key : Z) (ents : list (Z * (Z * Z))) (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (emh_entry I)) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 obj -> a1 = Z_to_bv 64 keyp ->

      umapx MI_A 24 (nval24 ASEGS) (lbl LB) m obj bl bc ents -> umap_sh m 24 (bl, bc, ents) ->
      Permutation LB (LB0 ++ LBm) -> Permutation (lbl LBm) (umap_blocks 24 bl bc ents) ->
      addressable m obj 40 -> wr_at asegs m obj 40 -> map_live_frame LF obj -> obj + 40 <= aceil ->
      (forall b, In b LB -> obj + 40 <= blk_addr b \/ blk_addr b + blk_size b <= obj) ->

      fldA m keyp 4 key -> accessible m keyp 4 -> emp_src H LB0 (bv_unsigned sp) obj keyp 4 ->
      (exists f, In f LF /\ ff_addr f <= keyp /\ keyp + 4 <= ff_addr f + fsz (ff_class f)) ->
      keyp mod 4 = 0 -> 0 <= key < 2 ^ 32 ->

      Zlength ents + 1 < 2 ^ 24 -> bc <> BSEQ_LAST ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
      lb_small LB + 24 + nsmall (8 * bseq_next bc) <= RT_SMALL_MAX -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX ->
      nlarge LB + nlg (8 * bseq_next bc) <= RT_LARGE_MAX ->
      ((bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [emp_del_ra (emh_emp I)] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AEMH_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE_BP)%nat -> relro0 m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
      lb_own LBm m ->
      as_SR H (emh_SB I ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LB0 LBm LF obj bl bc keyp key ents lo B shi m mo) (mkCfg msF mo).

  Definition emh_fromB_stmt (I : emh_inst) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe)
           (obj bl bc keyp key : Z) (ents : list (Z * (Z * Z))) (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (emh_entry I)) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 obj -> a1 = Z_to_bv 64 keyp ->

      umapx MI_A 24 (nval24 ASEGS) (lbl LB) m obj bl bc ents -> umap_sh m 24 (bl, bc, ents) ->
      Permutation LB (LB0 ++ LBm) -> Permutation (lbl LBm) (umap_blocks 24 bl bc ents) ->
      addressable m obj 40 -> wr_at asegs m obj 40 -> map_live_frame LF obj -> obj + 40 <= aceil ->
      (forall b, In b LB -> obj + 40 <= blk_addr b \/ blk_addr b + blk_size b <= obj) ->

      fldA m keyp 4 key -> accessible m keyp 4 -> emp_src H LB0 (bv_unsigned sp) obj keyp 4 ->
      (exists f, In f LF /\ ff_addr f <= keyp /\ keyp + 4 <= ff_addr f + fsz (ff_class f)) ->
      keyp mod 4 = 0 -> 0 <= key < 2 ^ 32 ->

      Zlength ents + 1 < 2 ^ 24 -> bc <> BSEQ_LAST ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
      lb_small LB + 24 + nsmall (8 * bseq_next bc) <= RT_SMALL_MAX -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX ->
      nlarge LB + nlg (8 * bseq_next bc) <= RT_LARGE_MAX ->
      ((bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [emp_del_ra (emh_emp I)] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AEMH_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE_BP)%nat -> relro0 m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
      lb_own LBm m ->
      forall cf, emh_SB I ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LB0 LBm LF obj bl bc keyp key ents lo B shi m mo cf -> as_SR H (emh_post H I ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LF obj bl bc key ents lo B shi m mo) cf.

  Definition emh_BC_stmt (I : emh_inst) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe)
           (obj bl bc keyp key : Z) (ents : list (Z * (Z * Z))) (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (emh_entry I)) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 obj -> a1 = Z_to_bv 64 keyp ->

      umapx MI_A 24 (nval24 ASEGS) (lbl LB) m obj bl bc ents -> umap_sh m 24 (bl, bc, ents) ->
      Permutation LB (LB0 ++ LBm) -> Permutation (lbl LBm) (umap_blocks 24 bl bc ents) ->
      addressable m obj 40 -> wr_at asegs m obj 40 -> map_live_frame LF obj -> obj + 40 <= aceil ->
      (forall b, In b LB -> obj + 40 <= blk_addr b \/ blk_addr b + blk_size b <= obj) ->

      fldA m keyp 4 key -> accessible m keyp 4 -> emp_src H LB0 (bv_unsigned sp) obj keyp 4 ->
      (exists f, In f LF /\ ff_addr f <= keyp /\ keyp + 4 <= ff_addr f + fsz (ff_class f)) ->
      keyp mod 4 = 0 -> 0 <= key < 2 ^ 32 ->

      Zlength ents + 1 < 2 ^ 24 -> bc <> BSEQ_LAST ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
      lb_small LB + 24 + nsmall (8 * bseq_next bc) <= RT_SMALL_MAX -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX ->
      nlarge LB + nlg (8 * bseq_next bc) <= RT_LARGE_MAX ->
      ((bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [emp_del_ra (emh_emp I)] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AEMH_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE_BP)%nat -> relro0 m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
      lb_own LBm m ->
      forall cf, emh_SB I ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LB0 LBm LF obj bl bc keyp key ents lo B shi m mo cf -> as_SR H (emh_SC I ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LB0 LBm LF obj bl bc keyp key ents lo B shi m mo) cf.

  Definition emh_Cpost_stmt (I : emh_inst) : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB LB0 LBm : list block) (LF : list fframe)
           (obj bl bc keyp key : Z) (ents : list (Z * (Z * Z))) (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 (emh_entry I)) fc None m (seg_rom asegs) ->
      frm_zero fc ->
      a0 = Z_to_bv 64 obj -> a1 = Z_to_bv 64 keyp ->

      umapx MI_A 24 (nval24 ASEGS) (lbl LB) m obj bl bc ents -> umap_sh m 24 (bl, bc, ents) ->
      Permutation LB (LB0 ++ LBm) -> Permutation (lbl LBm) (umap_blocks 24 bl bc ents) ->
      addressable m obj 40 -> wr_at asegs m obj 40 -> map_live_frame LF obj -> obj + 40 <= aceil ->
      (forall b, In b LB -> obj + 40 <= blk_addr b \/ blk_addr b + blk_size b <= obj) ->

      fldA m keyp 4 key -> accessible m keyp 4 -> emp_src H LB0 (bv_unsigned sp) obj keyp 4 ->
      (exists f, In f LF /\ ff_addr f <= keyp /\ keyp + 4 <= ff_addr f + fsz (ff_class f)) ->
      keyp mod 4 = 0 -> 0 <= key < 2 ^ 32 ->

      Zlength ents + 1 < 2 ^ 24 -> bc <> BSEQ_LAST ->

      as_RHEAP H s LB m -> as_AKREL H s (mkCfg msF mo) -> 0 <= as_AL H s ->
      lb_small LB + 24 + nsmall (8 * bseq_next bc) <= RT_SMALL_MAX -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX ->
      nlarge LB + nlg (8 * bseq_next bc) <= RT_LARGE_MAX ->
      ((bc = 0 \/ Zlength ents = bc) -> ICM (8 * bseq_next bc) <= as_AL H s) ->
      trace_ok (as_TR H) APC0_FREE [emp_del_ra (emh_emp I)] ->
      as_rauxv_ok H m B -> bv_unsigned sp <= B -> B < 2^64 ->

      bv_unsigned sp mod 16 = 0 ->
      stk asegs m lo (bv_unsigned sp) -> aceil <= lo -> lo <= bv_unsigned sp - AEMH_STACK ->
      rw_cells asegs m (errno_addr tp) [C4 errv] -> mem_inv asegs m -> tp = Z_to_bv 64 ATP ->
      bv_unsigned ra mod 2 = 0 ->
      ACONST m -> as_RFS H LF m -> (length LF < AFS_MAXLIVE_BP)%nat -> relro0 m -> stack0 m lo shi -> bv_unsigned sp <= shi ->
      lb_own LBm m ->
      forall cf, emh_SC I ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LB0 LBm LF obj bl bc keyp key ents lo B shi m mo cf -> as_SR H (emh_post H I ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s LB0 LF obj bl bc key ents lo B shi m mo) cf.
End EmhI.

Section EmhOkI.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.

  Lemma emh_ok : forall I, emh_toB_stmt H I -> emh_fromB_stmt H I -> emh_stmt H I.
  Proof using HHbp.
    intros I T1 T2. unfold emh_stmt. intros.
    eapply (ah_seq H (rt_bp_base H HHbp)); [eapply T1; eassumption | intros cf HB; eapply T2; eassumption].
  Qed.

  Lemma emh_from_B : forall I, emh_BC_stmt H I -> emh_Cpost_stmt H I -> emh_fromB_stmt H I.
  Proof using HHbp.
    intros I T1 T2. unfold emh_fromB_stmt. intros.
    eapply (ah_seq H (rt_bp_base H HHbp)); [eapply T1; eassumption | intros cf1 HC; eapply T2; eassumption].
  Qed.
End EmhOkI.
