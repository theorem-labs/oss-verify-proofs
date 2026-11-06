(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/Prog/fourbyte_strstr_c.v: ported from a working branch affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/B/Prog/fourbyte_strstr_c.v, which equals the A->B relocation (Theorem Labs tools) of lib/A/Prog/fourbyte_strstr_c.v at a working branch 5d8d8a15571 modulo module paths; module paths for this tree. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.B Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.A.Spec Require Import StrStr.
Import ListNotations.
Open Scope Z_scope.

Definition FOURBYTE_STRSTR : Z := 0x933f8.

Definition fourbyte_strstr_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (fc : bv 32) (a0 : word) (hb n4 : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word,
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (strstr_val (bv_unsigned a0) hb n4)) a1 a2 a3 a4 a5 a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m (seg_rom rsegs).

Definition fourbyte_strstr_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (hb n4 : list byte),
    bytes_at rsegs m (bv_unsigned a0) (hb ++ [Z_to_bv 8 0]) -> ~ In (Z_to_bv 8 0) hb -> (3 <= length hb)%nat ->
    bytes_at rsegs m (bv_unsigned a1) n4 -> length n4 = 4%nat -> ~ In (Z_to_bv 8 0) n4 ->
    evt rsegs (fourbyte_strstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 hb n4 m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 FOURBYTE_STRSTR) fc None m (seg_rom rsegs)).
