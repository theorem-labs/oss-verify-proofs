From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Prog Require Import strspn_c strcspn_c.
Import ListNotations.
Open Scope bv_scope.

Definition STRTOK_R : Z := 0x2124c.

Definition tok_i (sep str : list byte) : nat := spn_len sep str.

Definition tok_j (sep str : list byte) : nat := tok_i sep str + cspn_len sep (skipn (tok_i sep str) str).

Definition tok_ret (C : Z) (sep str : list byte) : Z :=
  if (C =? 0)%Z || Nat.eqb (tok_i sep str) (length str) then 0%Z else (C + Z.of_nat (tok_i sep str))%Z.

Definition tok_save (C : Z) (sep str : list byte) : Z :=
  if (C =? 0)%Z || Nat.leb (length str) (tok_j sep str) then 0%Z else (C + Z.of_nat (tok_j sep str) + 1)%Z.

Definition tok_cut (sep str : list byte) : list byte :=
  if Nat.ltb (tok_j sep str) (length str)
  then firstn (tok_j sep str) str ++ Z_to_bv 8 0 :: skipn (S (tok_j sep str)) str
  else str.

Definition strtok_r_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (P C : Z) (sep str slack : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (tok_ret C sep str)) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 128, bv_unsigned sp); (P, P + 8);
              (C + Z.of_nat (tok_j sep str), C + Z.of_nat (tok_j sep str) + 1)]%Z m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ rw_cells rsegs m' P [C8 (Z_to_bv 64 (tok_save C sep str))]
    /\ (C <> 0 -> u8arr rsegs m' C (tok_cut sep str ++ [Z_to_bv 8 0])
                  /\ bytes_at rsegs m' (C + Z.of_nat (length str) + 1) slack)%Z.

Definition strtok_r_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (C : Z) (pv : word) (str slack sep : list byte) (lo : Z) (can : word),
  rw_cells rsegs m (bv_unsigned a2) [C8 pv] ->
  C = (if bv_unsigned a0 =? 0 then bv_unsigned pv else bv_unsigned a0)%Z ->
  (C <> 0 ->
     u8arr rsegs m C (str ++ [Z_to_bv 8 0]) /\ bytes_at rsegs m (C + Z.of_nat (length str) + 1) slack
     /\ ((length sep <= 1)%nat -> (- (C + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))
     /\ (C + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= C)
     /\ (C + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= bv_unsigned a2 \/ bv_unsigned a2 + 8 <= C))%Z ->
  ~ In (Z_to_bv 8 0) str ->
  bytes_at rsegs m (bv_unsigned a1) (sep ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) sep ->
  bytes_at rsegs m SSP_GOT (le8 (Z_to_bv 64 SSP_GUARD)) -> bytes_at rsegs m SSP_GUARD (le8 can) ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 128 <= bv_unsigned sp)%Z ->
  (bv_unsigned a1 + Z.of_nat (length sep) + 1 <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (bv_unsigned a2 + 8 <= lo \/ bv_unsigned sp <= bv_unsigned a2)%Z ->
  (SSP_GOT + 8 <= lo \/ bv_unsigned sp <= SSP_GOT)%Z ->
  (SSP_GUARD + 8 <= lo \/ bv_unsigned sp <= SSP_GUARD)%Z ->
  mem_inv rsegs m ->
  evt rsegs (strtok_r_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bv_unsigned a2) C sep str slack lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRTOK_R) fc None m (seg_rom rsegs)).
