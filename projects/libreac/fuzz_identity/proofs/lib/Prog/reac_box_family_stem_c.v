From Stdlib Require Import ZArith List String Ascii.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_identity.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_identity.lib Require Import Img0.
Import ListNotations.
Open Scope Z_scope.

Definition REAC_BOX_FAMILY_STEM : Z := 0x13f74.
Definition STEM_T : Z := 0x1dea8.

Definition STEM_cstr (s : string) : list byte :=
  map (fun c => Z_to_bv 8 (Z.of_nat (nat_of_ascii c))) (list_ascii_of_string s) ++ [Z_to_bv 8 0].

Definition STEM (f : Z) : list byte :=
  STEM_cstr (if f =? 1 then "S-0808"%string
             else if f =? 2 then "S-1608"%string
             else if f =? 3 then "S-4000S"%string
             else "REAC"%string).

Definition STEM_Addr (f : Z) : Z :=
  if f =? 1 then 0x102d0
  else if f =? 2 then 0x103a4
  else if f =? 3 then 0x104e9
  else 0x10533.

Definition reac_box_family_stem_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (f : Z),
    -2^31 <= f < 2^31 -> a0 = Z_to_bv 64 f ->
    bytes_at rsegs m STEM_T (le8 (Z_to_bv 64 0x102d0) ++ le8 (Z_to_bv 64 0x103a4) ++ le8 (Z_to_bv 64 0x104e9)) ->
    evt rsegs
      (fun ms' => exists a1' : word,
         ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (STEM_Addr f)) a1' a2 a3 a4 a5 a6 a7
                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (ret_pc ra) fc None m (seg_rom rsegs) /\
         ro_bytes rsegs (STEM_Addr f) (STEM f))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 REAC_BOX_FAMILY_STEM) fc None m (seg_rom rsegs)).
