From Stdlib Require Import ZArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells FP.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.U.Prog Require Import Boxreg printf_facts_c snprintf_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOXREG_SET_NAME : Z := 0x13f6c.
Definition FMT_S : Z := 0x10305.
Definition EMPTY_S : Z := 0x102cd.

Definition name_ok (m : word -> option byte) (S lo r q : Z) (s : list Z) : Prop :=
  (q = 0 /\ s = []) \/
  (q <> 0 /\ Forall (fun c => 0 < c < 256) s /\ Z.of_nat (length s) < 2^31 - 1 /\
   exists slack : list byte,
     bytes_at rsegs m q (pf_bytes (s ++ [0]) ++ slack) /\
     (- (q + Z.of_nat (length s) + 1)) mod 8 <= Z.of_nat (length slack) /\
     (q + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= lo \/ S <= q) /\
     (q + Z.of_nat (length s) + 1 + Z.of_nat (length slack) <= r \/ r + 288 <= q)).

Definition reac_boxreg_set_name_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo r idx q : Z) (bs : list byte)
         (canary : word) (s : list Z),
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 idx -> a2 = Z_to_bv 64 q ->
    -2^31 <= idx < 2^31 ->
    rw_cells rsegs m r [CB 288 bs] -> boxreg_B1 bs -> pf_img_free r 288 -> r <> 0 -> r mod 4 = 0 ->
    name_ok m (bv_unsigned sp) lo r q s ->
    stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - SNPRINTF_K -> IMG_END <= lo ->
    bv_unsigned sp < 2^63 ->
    (r + 288 <= lo \/ bv_unsigned sp <= r) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (Ft : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Ft (ret_pc ra) fc' None m' (seg_rom rsegs) /\
         munch [(lo, bv_unsigned sp); (r + 56 * idx + 24, r + 56 * idx + 56)] m m' /\
         wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m' /\ frm0 fc' /\
         (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) /\
         stk rsegs m' lo (bv_unsigned sp) /\
         (if (idx <? 0) || (bx_n bs <=? idx) then m' = m /\ Ft = F /\ fc' = fc
          else bytes_at rsegs m' (r + 56 * idx + 24) (pf_bytes (firstn 31 s ++ [0]))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOXREG_SET_NAME) fc None m (seg_rom rsegs)).
