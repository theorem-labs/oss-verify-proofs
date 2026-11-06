From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge FP.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import LLVMFuzzerTestOneInput_c slot_inv slot_lib.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import printf_facts_c snprintf_c reac_box_name_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_table_c disco_json_text reac_disco_table_json_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import disco_jscalar_model disco_json_reader_model.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import json_scalar_c jtok_is_c.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require MemNorm.
Import ListNotations.
Open Scope Z_scope.

Definition SER_IN : Z := 0x135b8.
Definition SER_MALLOC : Z := 0x17330.
Definition SER_RET : Z := 0x135e4.
Definition SER_JSON : Z := 0x13660.
Definition SER_R12 : Z := 0x140bc.
Definition SER_FREE : Z := 0x171f0.
Definition SER_FREE_RET : Z := 0x14324.

Definition ser_k (op : Z) : Z := Z.land (Z.shiftr op 2) 31.
Definition ser_cap (op : Z) : Z := if ser_k op =? 0 then 1280 else 41 * ser_k op - 39.
Definition ser_capz (op : Z) : Z := ser_cap op + (if ser_cap op =? 0 then 1 else 0).

Definition js_table : list byte := le8 (Z_to_bv 64 0x103aa) ++ le8 (Z_to_bv 64 0x10298) ++ le8 (Z_to_bv 64 0x10326).

Definition slot24 (buf : Z) (vpad : list byte) (t : tokv) : list byte :=
  if tv_kind t =? 0 then repeat (Z_to_bv 8 0) 24
  else le8 (Z_to_bv 64 (buf + snd (fst t))) ++ le8 (Z_to_bv 64 (snd t)) ++ le4 (Z_to_bv 64 (tv_kind t)) ++ vpad.

Definition obj_bytes (buf : Z) (vpad : list byte) (o : jobj) : list byte := concat (map (slot24 buf vpad) o).

Definition objs_bytes (buf : Z) (vpad : list byte) (os : list jobj) : list byte :=
  concat (map (obj_bytes buf vpad) os).

Definition ser_J_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (X lo buf now count : Z) (B : list Z) (os : list jobj) (j192 j216 j224 jk jo jv : list byte),
    sp = Z_to_bv 64 X -> s0 = Z_to_bv 64 32 -> s2 = Z_to_bv 64 WS_MASK -> s8 = Z_to_bv 64 (X + 2336) ->
    s3 = Z_to_bv 64 buf -> s4 = Z_to_bv 64 (Z.of_nat (length B)) -> s11 = Z_to_bv 64 now ->
    0 < X -> X mod 16 = 0 -> X + 2592 < 2 ^ 63 -> 0 <= now < 2 ^ 64 ->
    0 < buf -> buf + Z.of_nat (length B) + 1 <= lo ->
    Forall (fun c => 33 <= c <= 255) B ->
    json_read B 9 = Some (count, os) -> count <= 8 ->
    bytes_at rsegs m buf (pf_bytes (B ++ [0])) ->
    rw_cells rsegs m (X + 192) [CB 8 j192] -> rw_cells rsegs m (X + 200) [C8 (Z_to_bv 64 now)] ->
    rw_cells rsegs m (X + 216) [CB 8 j216] -> rw_cells rsegs m (X + 224) [CB 8 j224] ->
    rw_cells rsegs m (X + 992) [CB 32 jk] -> rw_cells rsegs m (X + 1024) [CB 1296 jo] ->
    rw_cells rsegs m (X + 2320) [CB 24 jv] ->
    bytes_at rsegs m JSON_SCALAR_L js_table ->
    mem_inv rsegs m -> stk rsegs m lo X -> lo + JSON_SCALAR_K <= X -> IMG_END <= lo ->
    evt rsegs
      (fun ms' => exists (ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' s5' s7' s9' s10' t3' t4' t5' t6' : word)
                         (m' : word -> option byte) (vpad j192' j216' j224' jk' jo' jv' : list byte),
         ms' = MS (mkR ra' sp gp tp t0' t1' t2' s0 s1' a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5' (Z_to_bv 64 count) s7' s8 s9' s10' s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 SER_R12) fc None m' (seg_rom rsegs) /\
         munch [(lo, X); (X + 192, X + 200); (X + 216, X + 232); (X + 992, X + 2344)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo X /\
         rw_cells rsegs m' (X + 192) [CB 8 j192'] /\ rw_cells rsegs m' (X + 216) [CB 8 j216'] /\
         rw_cells rsegs m' (X + 224) [CB 8 j224'] /\ rw_cells rsegs m' (X + 992) [CB 32 jk'] /\
         rw_cells rsegs m' (X + 1024) [CB (Z.to_nat (144 * count)) (objs_bytes buf vpad os)] /\
         rw_cells rsegs m' (X + 1024 + 144 * count) [CB (Z.to_nat (1296 - 144 * count)) jo'] /\
         rw_cells rsegs m' (X + 2320) [CB 24 jv'] /\ length vpad = 4%nat)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SER_JSON) fc None m (seg_rom rsegs)).

Definition ser_P3_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (canary : word)
         (X lo buf now i p count : Z) (T : list byte) (os : list jobj)
         (vpad j0 jage jwid jtok jused jnm jscr : list byte),
    sp = Z_to_bv 64 X -> s3 = Z_to_bv 64 buf -> s6 = Z_to_bv 64 count -> s11 = Z_to_bv 64 now ->
    0 < X -> X mod 16 = 0 -> X + 2592 < 2 ^ 63 -> 0 <= now < 2 ^ 64 -> 0 < buf ->
    length T = 400%nat -> disco_table_c.table_ok T -> length vpad = 4%nat ->
    json_read (tj_text T now) 9 = Some (count, os) ->
    buf + Z.of_nat (length (tj_text T now)) + 1 <= lo ->
    bytes_at rsegs m buf (pf_bytes (tj_text T now ++ [0])) ->
    rw_cells rsegs m (X + 512) [CB 400 T] ->
    rw_cells rsegs m (X + 1024) [CB (Z.to_nat (144 * count)) (objs_bytes buf vpad os)] ->
    rw_cells rsegs m X [CB 16 j0] -> rw_cells rsegs m (X + 160) [C8 (Z_to_bv 64 i)] ->
    rw_cells rsegs m (X + 184) [C8 (Z_to_bv 64 p)] -> rw_cells rsegs m (X + 208) [C8 (Z_to_bv 64 W0X0)] ->
    rw_cells rsegs m (X + 920) [CB 24 jage] -> rw_cells rsegs m (X + 944) [CB 24 jwid] ->
    rw_cells rsegs m (X + 968) [CB 24 jtok] -> rw_cells rsegs m (X + 992) [CB 32 jused] ->
    rw_cells rsegs m (X + 2320) [CB 24 jnm] -> rw_cells rsegs m (X + 2344) [CB 144 jscr] ->
    bytes_at rsegs m BN_TS bn_table ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m -> stk rsegs m lo X -> lo + SNPRINTF_K <= X -> IMG_END <= lo ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' s4' s5' s6' s9' s10' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte)
                         (j0' jage' jwid' jtok' jused' jnm' jscr' : list byte),
         ms' = MS (mkR (Z_to_bv 64 SER_FREE_RET) sp gp tp t0' t1' t2' s0 (Z_to_bv 64 i) (Z_to_bv 64 buf)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4' s5' s6' (Z_to_bv 64 p) s8 s9' s10' s11 t3' t4' t5' t6')
                  F' (Z_to_bv 64 SER_FREE) fc' None m' (seg_rom rsegs) /\
         frm0 fc' /\ (forall k : reg, bv_unsigned k <> 10 -> reg_get F' k = reg_get F k) /\
         munch [(lo, X); (X, X + 16); (X + 920, X + 1024); (X + 2320, X + 2488)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ stk rsegs m' lo X /\
         rw_cells rsegs m' X [CB 16 j0'] /\
         rw_cells rsegs m' (X + 920) [CB 24 jage'] /\ rw_cells rsegs m' (X + 944) [CB 24 jwid'] /\
         rw_cells rsegs m' (X + 968) [CB 24 jtok'] /\ rw_cells rsegs m' (X + 992) [CB 32 jused'] /\
         rw_cells rsegs m' (X + 2320) [CB 24 jnm'] /\ rw_cells rsegs m' (X + 2344) [CB 144 jscr'])
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 SER_R12) fc None m (seg_rom rsegs)).
