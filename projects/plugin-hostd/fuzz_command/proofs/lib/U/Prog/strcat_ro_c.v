From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require MemNorm RoAdapt.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strcat_c.
Import ListNotations.
Open Scope bv_scope.

Definition strcat_post_ro (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 : word) (dstr str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp);
              (bv_unsigned a0 + Z.of_nat (length dstr), bv_unsigned a0 + Z.of_nat (length dstr) + Z.of_nat (length str) + 1)]%Z m m'
    /\ wmono rsegs m m' /\ MemNorm.ro_agree rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (dstr ++ str ++ [Z_to_bv 8 0])
    /\ rw_cells rsegs m' (bv_unsigned a0 + Z.of_nat (length dstr))%Z [CB (S (length str)) (str ++ [Z_to_bv 8 0])]
    /\ bytes_at rsegs m' (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack).

Definition strcat_ro_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (dstr dslack str slack junk : list byte) (lo : Z),
  bytes_at rsegs m (bv_unsigned a0) (dstr ++ Z_to_bv 8 0 :: dslack) ->
  ~ In (Z_to_bv 8 0) dstr ->
  ((- (bv_unsigned a0 + Z.of_nat (length dstr) + 1)) mod 8 <= Z.of_nat (length dslack))%Z ->
  rw_cells rsegs m (bv_unsigned a0 + Z.of_nat (length dstr))%Z [CB (S (length str)) junk] ->
  RoAdapt.not_ro rsegs (bv_unsigned a0 + Z.of_nat (length dstr))%Z (Z.of_nat (cells_size [CB (S (length str)) junk])) ->
  bytes_at rsegs m (bv_unsigned a1) (str ++ Z_to_bv 8 0 :: slack) ->
  ~ In (Z_to_bv 8 0) str ->
  ((- (bv_unsigned a1 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z ->
  (bv_unsigned a1 + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= bv_unsigned a0 + Z.of_nat (length dstr)
   \/ bv_unsigned a0 + Z.of_nat (length dstr) + Z.of_nat (length str) + 1 <= bv_unsigned a1)%Z ->
  stk rsegs m lo (bv_unsigned sp) -> RoAdapt.not_ro rsegs lo ((bv_unsigned sp) - lo) -> (lo + 48 <= bv_unsigned sp)%Z ->
  (bv_unsigned a0 + (Z.of_nat (length dstr) + 1 + Z.of_nat (length dslack)) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a0 + Z.of_nat (length dstr) + Z.of_nat (length str) + 1 <= lo
   \/ bv_unsigned sp <= bv_unsigned a0 + Z.of_nat (length dstr))%Z ->
  (bv_unsigned a1 + (Z.of_nat (length str) + 1 + Z.of_nat (length slack)) <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  MemNorm.ro_agree rsegs m ->
  evt rsegs (strcat_post_ro ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 dstr str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRCAT) fc None m (seg_rom rsegs)).
