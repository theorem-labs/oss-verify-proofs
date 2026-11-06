From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import LedgerCells.
Import ListNotations.
Open Scope Z_scope.

(* Measured in the symtab of agents/pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.plain (sha256 c8f4d6b8...), whose
   SHF_ALLOC sections equal those of the pinned fuzz_preset.plain 805604bb... except .note.gnu.build-id:
     fuzz_alloc_peak_reset FUNC   GLOBAL 0x15888 size 20
     g_live                OBJECT LOCAL  0x347b0 size 8
     g_peak                OBJECT LOCAL  0x347b8 size 8
   The body changed, not only moved: auipc a0; addi a0, a0, -0xe0 (= g_ran_out 0x347a8); ld a1, 8(a0); sd a1, 0x10(a0);
   ret, where the old one based a0 at g_live and used offsets 0 and 8. The effect is the same. *)
Definition FUZZ_ALLOC_PEAK_RESET : Z := 0x15888.
Definition G_LIVE : Z := Eval cbv in GL_LIVE.
Definition G_PEAK : Z := Eval cbv in GL_PEAK.

Definition fuzz_alloc_peak_reset_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (live : word),
    bytes_at rsegs m G_LIVE (le8 live) ->
    wr_at rsegs m G_PEAK 8 ->
    evt rsegs
      (fun ms' => exists (a0' a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' G_PEAK (le8 live) /\
         munch [(G_PEAK, G_PEAK + 8)] m m' /\
         wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FUZZ_ALLOC_PEAK_RESET) fc None m (seg_rom rsegs)).
