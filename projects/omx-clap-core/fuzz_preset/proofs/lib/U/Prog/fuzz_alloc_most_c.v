From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.U.Prog Require Import LedgerCells.
Import ListNotations.
Open Scope Z_scope.

(* fuzz_alloc_most (alloc.c :186-189 of the #102 source, sha256 6423eaae23e19ab3): g_most = n. NEW in #102; its one
   caller is LLVMFuzzerTestOneInput (fuzz_preset.c:810, fuzz_alloc_most(PJ_ALLOC_BOUND(size))).
   Measured in the symtab of agents/pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.ubsan (sha256
   27566683...), whose SHF_ALLOC sections equal those of the pinned fuzz_preset.ubsan 45b0357d... except .note.gnu.build-id:
     fuzz_alloc_most FUNC   GLOBAL 0x15fa8 size 12  (auipc a1, 0xf; sd a0, 0x38(a1); ret)
     g_most          OBJECT LOCAL  0x24fe0 size 8   (.data; LedgerCells.GL_MOST, generated from the same symtab)
   No frame, no call: a0 (n) is kept, a1 is the auipc result, every other register and every byte outside g_most's
   8 bytes is kept. *)
Definition FUZZ_ALLOC_MOST : Z := 0x15fa8.
Definition G_MOST : Z := Eval cbv in GL_MOST.

Definition fuzz_alloc_most_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte),
    wr_at rsegs m G_MOST 8 ->
    evt rsegs
      (fun ms' => exists (a1' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' G_MOST (le8 a0) /\
         munch [(G_MOST, G_MOST + 8)] m m' /\
         wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FUZZ_ALLOC_MOST) fc None m (seg_rom rsegs)).
