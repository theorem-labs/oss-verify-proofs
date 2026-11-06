From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import tolower_c.
Import ListNotations.
Open Scope bv_scope.

Definition STRNCASECMP : Z := 0x1c778.

Definition ncase_eq (ls rs : list byte) (n : Z) : Prop :=
  map zlower (firstn (Z.to_nat n) (map bv_unsigned ls ++ [0%Z]))
  = map zlower (firstn (Z.to_nat n) (map bv_unsigned rs ++ [0%Z])).

Definition strncasecmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (ls rs : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists r t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 r a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp)
    /\ bytes_at rsegs m' (bv_unsigned a0) (ls ++ [Z_to_bv 8 0])
    /\ bytes_at rsegs m' (bv_unsigned a1) (rs ++ [Z_to_bv 8 0])
    /\ (r = Z_to_bv 64 0 <-> ncase_eq ls rs (bv_unsigned a2)).

Definition strncasecmp_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (ls rs : list byte) (lo : Z),
  stk rsegs m lo (bv_unsigned sp) ->
  bytes_at rsegs m (bv_unsigned a0) (ls ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) ls ->
  bytes_at rsegs m (bv_unsigned a1) (rs ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) rs ->
  mem_inv rsegs m ->
  (lo <= bv_unsigned sp - 48)%Z ->
  (bv_unsigned a0 + Z.of_nat (length ls) + 1 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length rs) + 1 <= bv_unsigned sp - 48 \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  evt rsegs (strncasecmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 ls rs lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRNCASECMP) fc None m (seg_rom rsegs)).
