From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Cells Step Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require MemNorm.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.Spec Require FloatScan.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.CJ.P Require FmtFp_facts3.
Import ListNotations.
Open Scope Z_scope.

Definition STRTOD : Z := 0x1e328.
Definition STRTOD_K : Z := 8928.
Definition STRTOD_TP : Z := 0x33c28.
Definition STRTOD_ERRNO : Z := 0x33b84.
Definition STRTOD_GOT_GUARD : Z := 0x22888.
Definition STRTOD_GUARD : Z := 0x53e98.
Definition STRTOD_GLOBALS_TOP : Z := 0x55000.
Definition STRTOD_IMG_LO : Z := 0x10000.

Definition strtod_model (txt : list Z) : option (Z * Z) := FloatScan.scan_strtod (txt ++ [0]).

Definition strtod_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (s e : Z) (txt : list Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32)
                    (m' : word -> option byte) (ev' : word) (c bits : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F' (ret_pc ra) fc' None m' (seg_rom rsegs)
    /\ strtod_model txt = Some (bits, c) /\ 0 <= c <= Z.of_nat (length txt)
    /\ rw_cells rsegs m' e [C8 (Z_to_bv 64 (s + c))]
    /\ reg_get F' 10 = Z_to_bv 64 bits
    /\ (forall k : bv 5, bv_unsigned k <> 10 -> bv_unsigned k <> 14 -> bv_unsigned k <> 15 -> reg_get F' k = reg_get F k)
    /\ frm0 fc'
    /\ rw_cells rsegs m' STRTOD_ERRNO [C4 ev']
    /\ munch [(bv_unsigned sp - STRTOD_K, bv_unsigned sp); (e, e + 8); (STRTOD_ERRNO, STRTOD_ERRNO + 4)] m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ MemNorm.task_mem rsegs m'
    /\ stk rsegs m' (bv_unsigned sp - STRTOD_K) (bv_unsigned sp).

Definition strtod_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (s e : Z) (txt : list Z) (ejunk canary ev : word),
    a0 = Z_to_bv 64 s -> a1 = Z_to_bv 64 e -> tp = Z_to_bv 64 STRTOD_TP ->
    bytes_at rsegs m s (map (Z_to_bv 8) (txt ++ [0])) ->
    Forall (fun c => FmtFp_facts3.is_numch c = true) txt -> Z.of_nat (length txt) < 2^30 ->
    rw_cells rsegs m e [C8 ejunk] ->
    stk rsegs m (bv_unsigned sp - STRTOD_K) (bv_unsigned sp) ->
    STRTOD_GLOBALS_TOP <= bv_unsigned sp - STRTOD_K -> bv_unsigned sp < 2^62 ->
    4096 <= s -> s + Z.of_nat (length txt) + 1 <= 2^62 ->
    ((s + Z.of_nat (length txt) + 1 <= STRTOD_IMG_LO \/ STRTOD_GLOBALS_TOP <= s)
       /\ s + Z.of_nat (length txt) + 1 <= bv_unsigned sp - STRTOD_K
     \/ bv_unsigned sp <= s) ->
    (STRTOD_GLOBALS_TOP <= e /\ e + 8 <= bv_unsigned sp - STRTOD_K \/ bv_unsigned sp <= e) -> e + 8 <= 2^62 ->
    (e + 8 <= s \/ s + Z.of_nat (length txt) + 1 <= e) ->
    rw_cells rsegs m STRTOD_GOT_GUARD [C8 (Z_to_bv 64 STRTOD_GUARD)] -> rw_cells rsegs m STRTOD_GUARD [C8 canary] ->
    rw_cells rsegs m STRTOD_ERRNO [C4 ev] ->
    mem_inv rsegs m -> MemNorm.task_mem rsegs m -> frm0 fc ->
    evt rsegs (strtod_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F s e txt m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRTOD) fc None m (seg_rom rsegs)).
