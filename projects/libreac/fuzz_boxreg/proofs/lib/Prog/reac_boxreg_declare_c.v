From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step FP.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib Require MemNorm.
From OSSVerify.Proofs.libreac.fuzz_boxreg.lib.Prog Require Import Boxreg lowest_free_base_c printf_facts_c snprintf_c
  reac_boxreg_set_name_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOXREG_DECLARE : Z := 0x13864.
Definition DECLARE_K : Z := 6000.

Definition box_width_ok (k fabric : Z) : Prop :=
  Z.even k = true /\ 2 <= k <= 40 /\ k <= fabric.

Definition range_ok (bs : list byte) (k b : Z) : Prop :=
  0 <= b /\ b + k <= bx_fabric bs /\ ~ slice_meets bs b k.

Definition name_field (s : list Z) : list byte :=
  pf_bytes (firstn 31 s) ++ repeat (Z_to_bv 8 0) (32 - Nat.min (length s) 31).

Definition decl_row (b k p : Z) (s : list Z) : list byte :=
  repeat (Z_to_bv 8 0) 8 ++ le4 (Z_to_bv 64 b) ++ le4 (Z_to_bv 64 k) ++ le4 (Z_to_bv 64 0)
    ++ le4 (Z_to_bv 64 p) ++ name_field s.

Definition decl_bytes (bs : list byte) (b k p : Z) (s : list Z) : list byte :=
  upd_bytes (upd_bytes bs (Z.to_nat (56 * bx_n bs)) (decl_row b k p s)) 280
    (le4 (Z_to_bv 64 (bx_n bs + 1))).

Definition declare_refused (bs : list byte) (k b0 : Z) : Prop :=
  ~ box_width_ok k (bx_fabric bs) \/ 5 <= bx_n bs \/
  (0 <= b0 /\ ~ range_ok bs k b0) \/ (b0 < 0 /\ lowest_free bs k (-1)).

Definition declare_placed (bs : list byte) (k b0 b p : Z) : Prop :=
  box_width_ok k (bx_fabric bs) /\ bx_n bs < 5 /\
  ((0 <= b0 /\ b = b0 /\ p = 1 /\ range_ok bs k b0) \/
   (b0 < 0 /\ p = 0 /\ 0 <= b /\ lowest_free bs k b)).

Definition fkeep (F F' : bvmap 5 word) : Prop :=
  forall i : bv 5, bv_unsigned i <> 10 -> reg_get F' i = reg_get F i.

Definition reac_boxreg_declare_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (r k nm b0 lo : Z) (bs : list byte) (canary : word) (s : list Z),
    a0 = Z_to_bv 64 r -> a1 = Z_to_bv 64 k -> a2 = Z_to_bv 64 nm -> a3 = Z_to_bv 64 b0 ->
    -2^31 <= k < 2^31 -> -2^31 <= b0 < 2^31 -> 0 <= nm < 2^64 ->
    r mod 8 = 0 -> pf_img_free r 288 ->
    bytes_at rsegs m r bs -> wr_at rsegs m r 288 -> boxreg_inv bs ->
    name_ok m (bv_unsigned sp) lo r nm s ->
    stk rsegs m lo (bv_unsigned sp) -> lo + DECLARE_K <= bv_unsigned sp -> IMG_END <= lo -> bv_unsigned sp < 2^63 ->
    (bv_unsigned sp <= r \/ r + 288 <= lo) ->
    frm0 fc -> mem_inv rsegs m -> MemNorm.task_mem rsegs m ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 canary) ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (F' : bvmap 5 word) (fc' : bv 32) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F' (ret_pc ra) fc' None m' (seg_rom rsegs) /\
         fkeep F F' /\ frm0 fc' /\
         munch [(lo, bv_unsigned sp); (r, r + 288)] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m' /\
         MemNorm.task_mem rsegs m' /\
         stk rsegs m' lo (bv_unsigned sp) /\
         ((declare_refused bs k b0 /\ a0' = Z_to_bv 64 (-1) /\ bytes_at rsegs m' r bs) \/
          (exists b p, declare_placed bs k b0 b p /\ a0' = Z_to_bv 64 (bx_n bs) /\
                       bytes_at rsegs m' r (decl_bytes bs b k p s))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOXREG_DECLARE) fc None m (seg_rom rsegs)).

Definition reac_boxreg_declare_keeps_inv : Prop :=
  forall (bs : list byte) (s : list Z) (k b0 b p : Z),
    boxreg_inv bs -> declare_placed bs k b0 b p -> boxreg_inv (decl_bytes bs b k p s).
