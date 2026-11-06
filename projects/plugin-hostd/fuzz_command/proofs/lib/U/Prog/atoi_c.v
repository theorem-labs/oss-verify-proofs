From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U Require Import Img0.
From OSSVerify.Proofs.plugin_hostd.fuzz_command.lib.U.Spec Require Import CType.
Import ListNotations.
Open Scope Z_scope.

Definition ATOI : Z := 0x1fccc.

Fixpoint atoi_acc (n : Z) (s : list byte) : Z :=
  match s with
  | b :: s' => if c_digit b then atoi_acc (bv_swrap 32 (10 * n - (bv_unsigned b - 48))) s' else n
  | [] => n
  end.

Definition atoi_val (s : list byte) : Z :=
  match skip_space s with
  | b :: r =>
      if bv_unsigned b =? 45 then atoi_acc 0 r
      else if bv_unsigned b =? 43 then bv_swrap 32 (- atoi_acc 0 r)
      else bv_swrap 32 (- atoi_acc 0 (b :: r))
  | [] => 0
  end.

Definition atoi_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (str : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (atoi_val str)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [] m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'.

Definition atoi_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A : Z) (str : list byte),
    bytes_at rsegs m A (str ++ [Z_to_bv 8 0]) ->
    mem_inv rsegs m ->
    evt rsegs (atoi_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 A) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ATOI) fc None m (seg_rom rsegs)).
