From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import reac_disco_table_json_c slot_ser_defs.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import slot_inv printf_facts_c snprintf_c reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.U.Prog Require Import disco_table_c json_scalar_c.
Import ListNotations.
Open Scope Z_scope.

Definition uSER_IN : Z := 0x136ec.
Definition uSER_MALLOC : Z := 0x17aec.
Definition uSER_RET : Z := 0x13720.
Definition uSER_JSON : Z := 0x137a8.
Definition uSER_R12 : Z := 0x13f08.
Definition uSER_FREE : Z := 0x179ac.
Definition uSER_FREE_RET : Z := 0x1417c.

Definition user_J_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (X lo buf count : Z) (B : list Z) (os : list jobj) (j208 j232 jk jo jv : list byte),
    sp = Z_to_bv 64 X -> s1 = Z_to_bv 64 (nt buf) -> s2 = Z_to_bv 64 WS_MASK -> s3 = Z_to_bv 64 buf ->
    s4 = Z_to_bv 64 (Z.of_nat (length B)) -> s8 = Z_to_bv 64 (X + 2368) -> s10 = Z_to_bv 64 32 ->
    s11 = Z_to_bv 64 1 ->
    0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 ->
    0 < buf -> buf + Z.of_nat (length B) + 1 <= lo ->
    Forall (fun c => 33 <= c <= 255) B ->
    json_read B 9 = Some (count, os) -> count <= 8 ->
    bytes_at rsegs m buf (pf_bytes (B ++ [0])) ->
    rw_cells rsegs m (X + 176) [C8 (Z_to_bv 64 (nt (X + 1056)))] ->
    rw_cells rsegs m (X + 208) [CB 8 j208] -> rw_cells rsegs m (X + 216) [C8 (Z_to_bv 64 IMAX)] ->
    rw_cells rsegs m (X + 232) [CB 24 j232] ->
    rw_cells rsegs m (X + 1024) [CB 32 jk] -> rw_cells rsegs m (X + 1056) [CB 1296 jo] ->
    rw_cells rsegs m (X + 2352) [CB 24 jv] ->
    bytes_at rsegs m JSON_SCALAR_L js_table ->
    mem_inv rsegs m -> stk rsegs m lo X -> lo + JSON_SCALAR_K <= X -> IMG_END <= lo ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s0' a0' a1' a2' a3' a4' a5' a6' a7' s5' s6' s7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (vpad j208' j232' jk' jo' jv' : list byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0' s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5' s6' s7' s8 (Z_to_bv 64 count) s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 uSER_R12) fc None m' (seg_rom rsegs) /\
         munch [(lo, X); (X + 208, X + 216); (X + 232, X + 256); (X + 1024, X + 2376)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
         rw_cells rsegs m' (X + 208) [CB 8 j208'] /\ rw_cells rsegs m' (X + 232) [CB 24 j232'] /\
         rw_cells rsegs m' (X + 1024) [CB 32 jk'] /\
         rw_cells rsegs m' (X + 1056) [CB (Z.to_nat (144 * count)) (objs_bytes buf vpad os)] /\
         rw_cells rsegs m' (X + 1056 + 144 * count) [CB (Z.to_nat (1296 - 144 * count)) jo'] /\
         rw_cells rsegs m' (X + 2352) [CB 24 jv'] /\ length vpad = 4%nat)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 uSER_JSON) fc None m (seg_rom rsegs)).

Definition user_P3_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (canary : word)
         (X lo buf now count : Z) (T : list byte) (os : list jobj)
         (vpad j0 jage jwid jtok jused jnm jscr : list byte),
    sp = Z_to_bv 64 X -> s3 = Z_to_bv 64 buf -> s9 = Z_to_bv 64 count -> s11 = Z_to_bv 64 1 ->
    0 < X -> X mod 16 = 0 -> X + 2624 < 2 ^ 63 -> 0 <= now < 2 ^ 64 -> 0 < buf ->
    length T = 400%nat -> U.Prog.disco_table_c.table_ok T -> length vpad = 4%nat ->
    json_read (tj_text T now) 9 = Some (count, os) ->
    buf + Z.of_nat (length (tj_text T now)) + 1 <= lo ->
    bytes_at rsegs m buf (pf_bytes (tj_text T now ++ [0])) ->
    rw_cells rsegs m (X + 544) [CB 400 T] ->
    rw_cells rsegs m (X + 1056) [CB (Z.to_nat (144 * count)) (objs_bytes buf vpad os)] ->
    rw_cells rsegs m X [CB 16 j0] -> rw_cells rsegs m (X + 184) [C8 (Z_to_bv 64 W0X0)] ->
    rw_cells rsegs m (X + 192) [C8 (Z_to_bv 64 (nt (X + 1024)))] ->
    rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 (nt (X + 544)))] ->
    rw_cells rsegs m (X + 224) [C8 (Z_to_bv 64 now)] ->
    rw_cells rsegs m (X + 952) [CB 24 jage] -> rw_cells rsegs m (X + 976) [CB 24 jwid] ->
    rw_cells rsegs m (X + 1000) [CB 24 jtok] -> rw_cells rsegs m (X + 1024) [CB 32 jused] ->
    rw_cells rsegs m (X + 2352) [CB 24 jnm] -> rw_cells rsegs m (X + 2376) [CB 144 jscr] ->
    bytes_at rsegs m BN_TS bn_table ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m lo X -> lo + SNPRINTF_K <= X ->
    IMG_END <= lo ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' s0' s1' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s7' s9' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte)
                         (j0' jage' jwid' jtok' jused' jnm' jscr' : list byte),
         ms' = MS (mkR (Z_to_bv 64 uSER_FREE_RET) sp gp tp t0' t1' t2' s0' s1' (Z_to_bv 64 buf)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4' s5' s6' s7' s8 s9' s10 s11 t3' t4' t5' t6')
                  F' (Z_to_bv 64 uSER_FREE) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
         munch [(lo, X); (X, X + 16); (X + 952, X + 1056); (X + 2352, X + 2520)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo X /\
         rw_cells rsegs m' X [CB 16 j0'] /\
         rw_cells rsegs m' (X + 952) [CB 24 jage'] /\ rw_cells rsegs m' (X + 976) [CB 24 jwid'] /\
         rw_cells rsegs m' (X + 1000) [CB 24 jtok'] /\ rw_cells rsegs m' (X + 1024) [CB 32 jused'] /\
         rw_cells rsegs m' (X + 2352) [CB 24 jnm'] /\ rw_cells rsegs m' (X + 2376) [CB 144 jscr'])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 uSER_R12) fc None m (seg_rom rsegs)).
