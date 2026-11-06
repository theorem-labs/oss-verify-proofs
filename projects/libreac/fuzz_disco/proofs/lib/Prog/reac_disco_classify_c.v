From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame.
From OSSVerify.Proofs.libreac.fuzz_disco.lib Require Import Img0.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require Import CtrlParsed disco_classify_c classify_core_c.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_DISCO_CLASSIFY : Z := 0x1514c.

Definition reac_disco_classify_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo f len u o : Z) (FB U OB : list byte),
    a0 = Z_to_bv 64 f -> a1 = Z_to_bv 64 len -> a2 = Z_to_bv 64 u -> a3 = Z_to_bv 64 o ->
    classify_core_pre m (bv_unsigned sp) lo 0 f len u o FB U OB None ->
    evt rsegs (classify_core_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo 0 len o FB U OB None)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_DISCO_CLASSIFY) fc None m (seg_rom rsegs)).
