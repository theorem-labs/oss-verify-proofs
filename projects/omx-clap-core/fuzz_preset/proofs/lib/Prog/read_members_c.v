From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Spec Require Import PjTree.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Prog Require Import PjStruct.
Import ListNotations.
Open Scope Z_scope.

(* read_members (fuzz_preset.c:784-798 of the #102 source, sha256 c7b4007bba7bab3e), out of line in the #102 pins.
   Measured in the symtab of agents/pau-preset-102/omx-clap-core/unstripped/fuzz_preset/fuzz_preset.plain (sha256
   c8f4d6b8...): read_members FUNC LOCAL 0x13e58 size 396; addi sp, sp, -0x50 (saves ra, s0-s6; `seen` at sp+8); it calls
   only pj_get (0x15cb4, frame 48) and pj_get_str (0x15d48, frame 64), so it writes no byte outside its own frame and
   the frames of those two: RM_K = 80 + 64. Its one caller is LLVMFuzzerTestOneInput (0x13750, a0 = sp = &doc).
   The contract is the caller's (the entry walk); the body walk is h-verbs-1's. *)
Definition READ_MEMBERS : Z := 0x13e58.
Definition RM_F : Z := 80.
Definition RM_K : Z := RM_F + 64.

Definition read_members_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lblk : Z -> Z -> Prop)
         (o : Z) (t : jv) (D : list (Z * Z)) (lo : Z),
    a0 = Z_to_bv 64 o ->
    pj_node rsegs m lblk o t D ->
    (forall a n, lblk a n -> 0 < a /\ a mod 8 = 0 /\ a + n <= 2 ^ 47 /\
       disjoint_from [(a, a + n)] (bv_unsigned sp - RM_K) RM_K) ->
    bv_unsigned sp mod 16 = 0 -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - RM_K ->
    disjoint_from [(o, o + 56)] (bv_unsigned sp - RM_K) RM_K ->
    mem_inv rsegs m ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         munch [(bv_unsigned sp - RM_K, bv_unsigned sp)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo (bv_unsigned sp) /\ pj_node rsegs m' lblk o t D)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 READ_MEMBERS) fc None m (seg_rom rsegs)).
