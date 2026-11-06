From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.U Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition PUT_UTF8 : Z := 0x15d94.

Definition utf8 (cp : Z) : list byte :=
  if cp <? 0x80 then [Z_to_bv 8 cp]
  else if cp <? 0x800 then [Z_to_bv 8 (0xC0 + cp / 64); Z_to_bv 8 (0x80 + cp mod 64)]
  else if cp <? 0x10000 then
    [Z_to_bv 8 (0xE0 + cp / 4096); Z_to_bv 8 (0x80 + (cp / 64) mod 64); Z_to_bv 8 (0x80 + cp mod 64)]
  else
    [Z_to_bv 8 (0xF0 + cp / 262144); Z_to_bv 8 (0x80 + (cp / 4096) mod 64);
     Z_to_bv 8 (0x80 + (cp / 64) mod 64); Z_to_bv 8 (0x80 + cp mod 64)].

Definition put_utf8_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (o cp : Z),
    a0 = Z_to_bv 64 o ->
    a1 = Z_to_bv 64 cp ->
    o <> 0 ->
    wr_at rsegs m o (Z.of_nat (length (utf8 cp))) ->
    0 < cp <= 0x10FFFF ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (Z.of_nat (length (utf8 cp))))
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (ret_pc ra) fc None m' (seg_rom rsegs) /\
         bytes_at rsegs m' o (utf8 cp) /\
         munch [(o, o + Z.of_nat (length (utf8 cp)))] m m' /\
         wmono rsegs m m')
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PUT_UTF8) fc None m (seg_rom rsegs)).
