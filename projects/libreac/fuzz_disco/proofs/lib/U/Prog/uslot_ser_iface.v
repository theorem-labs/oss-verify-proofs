From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_json_c slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv printf_facts_c snprintf_c reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c json_scalar_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import uslot_ser_defs.
Import ListNotations.
Open Scope Z_scope.

Definition uSER_W (lo X buf cap : Z) : list (Z * Z) :=
  [(lo, X); (X, X + 16); (X + 208, X + 216); (X + 232, X + 256); (X + 952, X + 2520); (buf, buf + cap)].

Definition uslot_ser_chain_A : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (X op : Z) (j136 j152 : list byte),
    sp = Z_to_bv 64 X -> s9 = Z_to_bv 64 op -> 0 <= op < 256 -> 0 <= X -> X + 2624 <= 2 ^ 64 ->
    rw_cells rsegs m (X + 136) [CB 8 j136] -> rw_cells rsegs m (X + 152) [CB 8 j152] -> mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (a1' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 uSER_RET) sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (ser_capz op)) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 (Z_to_bv 64 (ser_cap op)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 uSER_MALLOC) fc None m' (seg_rom rsegs) /\
         munch [(X + 136, X + 144); (X + 152, X + 160)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         rw_cells rsegs m' (X + 136) [C8 s7] /\ rw_cells rsegs m' (X + 152) [C8 s6])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 uSER_IN) fc None m (seg_rom rsegs)).

Definition uslot_ser_chain_B : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (canary : word)
         (X lo buf cap now n h i p : Z)
         (T Lk Gt ob junk slk j0 j1 j2 j3 j4 j5 j6 jr jw : list byte) (sv : list cell),
    sp = Z_to_bv 64 X -> a0 = Z_to_bv 64 buf -> s2 = Z_to_bv 64 WS_MASK -> s5 = Z_to_bv 64 cap ->
    s8 = Z_to_bv 64 (X + 2368) -> s10 = Z_to_bv 64 32 -> s11 = Z_to_bv 64 1 ->
    0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 <= now < 2 ^ 64 ->
    2 <= cap <= 1280 -> 0 < buf -> buf mod 8 = 0 -> buf + cap + Z.of_nat (length slk) <= lo -> pf_img_free buf cap ->
    (- cap) mod 8 <= Z.of_nat (length slk) ->
    rw_cells rsegs m buf [CB (Z.to_nat cap) junk] -> bytes_at rsegs m (buf + cap) slk ->
    length T = 400%nat -> U.Prog.disco_table_c.table_ok T ->
    rw_cells rsegs m X (spill_cells j0 j1 j2 j3 j4 j5 j6 h X) ->
    rw_cells rsegs m (X + 136) [C8 (Z_to_bv 64 n)] -> rw_cells rsegs m (X + 152) [C8 (Z_to_bv 64 p)] ->
    rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 i)] -> rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] ->
    rw_cells rsegs m (X + OFF_LOCK) [CB 12 Lk] -> rw_cells rsegs m (X + OFF_GATE) [CB 264 Gt] ->
    rw_cells rsegs m (X + OFF_TABLE) [CB 400 T] -> rw_cells rsegs m (X + OFF_OUR) [CB 2 jr; CB 6 ob] ->
    rw_cells rsegs m (X + OFF_WORK) [CB 1568 jw] -> rw_cells rsegs m (X + OFF_SAVE) sv ->
    bytes_at rsegs m JSON_SCALAR_L js_table -> bytes_at rsegs m BN_TS bn_table ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    frm0 fc -> mem_inv rsegs m -> U.MemNorm.task_mem rsegs m -> stk rsegs m lo X ->
    lo + U.Prog.reac_disco_table_json_c.TJ_K <= X -> IMG_END <= lo ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s9' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte)
                         (j0' j4' j5' jw' : list byte),
         ms' = MS (mkR (Z_to_bv 64 uSER_FREE_RET) sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 buf)
                       a1' a2' a3' a4' a5' a6' a7' s2 (Z_to_bv 64 buf) s4' s5' s6' s7' s8 s9' s10 s11 t3' t4' t5' t6')
                  F' (Z_to_bv 64 uSER_FREE) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
         munch (uSER_W lo X buf cap) m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ U.MemNorm.task_mem rsegs m' /\
         stk rsegs m' lo X /\
         rw_cells rsegs m' X (spill_cells j0' j1 j2 j3 j4' j5' j6 h X) /\
         rw_cells rsegs m' (X + 136) [C8 (Z_to_bv 64 n)] /\ rw_cells rsegs m' (X + 152) [C8 (Z_to_bv 64 p)] /\
         rw_cells rsegs m' (X + 160) [C8 (Z_to_bv 64 i)] /\ rw_cells rsegs m' (X + 224) [C8 (Z_to_bv 64 now)] /\
         rw_cells rsegs m' (X + OFF_LOCK) [CB 12 Lk] /\ rw_cells rsegs m' (X + OFF_GATE) [CB 264 Gt] /\
         rw_cells rsegs m' (X + OFF_TABLE) [CB 400 T] /\ rw_cells rsegs m' (X + OFF_OUR) [CB 2 jr; CB 6 ob] /\
         rw_cells rsegs m' (X + OFF_WORK) [CB 1568 jw'] /\ rw_cells rsegs m' (X + OFF_SAVE) sv)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 uSER_RET) fc None m (seg_rom rsegs)).

Definition uslot_ser_chain : Prop := uslot_ser_chain_A /\ uslot_ser_chain_B.
