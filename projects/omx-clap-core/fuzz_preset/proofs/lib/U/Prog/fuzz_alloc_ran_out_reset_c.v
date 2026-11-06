From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import LedgerCells.
Import ListNotations.
Open Scope Z_scope.

(* Measured in the symtab of agents/pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.ubsan (sha256 27566683...), whose
   SHF_ALLOC sections equal those of the pinned fuzz_preset.ubsan 45b0357d... except .note.gnu.build-id:
     fuzz_alloc_ran_out_reset FUNC   GLOBAL 0x15f9c size 12  (auipc a0; sb zero, 0x2bc(a0); ret)
     g_ran_out                OBJECT LOCAL  0x35258 size 1   (static int g_ran_out is kept as one byte) *)
Definition FUZZ_ALLOC_RAN_OUT_RESET : Z := 0x15f9c.
Definition G_RAN_OUT : Z := Eval cbv in GL_RAN_OUT.

Definition fuzz_alloc_ran_out_reset_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    wr_at rsegs m G_RAN_OUT 1 ->
    evt rsegs
      (fun ms' => exists (a0' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1 a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' G_RAN_OUT (le1 (Z_to_bv 64 0)) /\
         munch [(G_RAN_OUT, G_RAN_OUT + 1)] m m' /\
         wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FUZZ_ALLOC_RAN_OUT_RESET) fc None m (seg_rom rsegs)).
