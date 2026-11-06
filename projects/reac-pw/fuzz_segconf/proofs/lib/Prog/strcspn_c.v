From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr Bytes.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib Require Import Img0.
Import ListNotations.
Open Scope bv_scope.

Definition STRCSPN : Z := 0x20b6c.
Definition CSPN_SSP_GOT : Z := 0x22a68.
Definition CSPN_SSP_GUARD : Z := 0x54450.

Fixpoint cspn_len (set s : list byte) : nat :=
  match s with
  | [] => O
  | x :: s' => if existsb (fun c => Z.eqb (bv_unsigned c) (bv_unsigned x)) set then O else S (cspn_len set s')
  end.

Definition strcspn_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (str set : list byte) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (Z.of_nat (cspn_len set str))) a1 a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m' /\ wmono rsegs m m' /\ mem_inv rsegs m'
    /\ stk rsegs m' lo (bv_unsigned sp).

Definition strcspn_contract : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (str slack set : list byte) (lo : Z) (can : word),
  bytes_at rsegs m (bv_unsigned a0) (str ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) str ->
  ((length set <= 1)%nat -> ((- (bv_unsigned a0 + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z) ->
  bytes_at rsegs m (bv_unsigned a1) (set ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) set ->
  bytes_at rsegs m CSPN_SSP_GOT (le8 (Z_to_bv 64 CSPN_SSP_GUARD)) -> bytes_at rsegs m CSPN_SSP_GUARD (le8 can) ->
  stk rsegs m lo (bv_unsigned sp) -> (lo + 96 <= bv_unsigned sp)%Z ->
  (bv_unsigned a0 + Z.of_nat (length str) + 1 + Z.of_nat (length slack) <= lo \/ bv_unsigned sp <= bv_unsigned a0)%Z ->
  (bv_unsigned a1 + Z.of_nat (length set) + 1 <= lo \/ bv_unsigned sp <= bv_unsigned a1)%Z ->
  (CSPN_SSP_GOT + 8 <= lo \/ bv_unsigned sp <= CSPN_SSP_GOT)%Z ->
  (CSPN_SSP_GUARD + 8 <= lo \/ bv_unsigned sp <= CSPN_SSP_GUARD)%Z ->
  mem_inv rsegs m ->
  evt rsegs (strcspn_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc str set lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 STRCSPN) fc None m (seg_rom rsegs)).
