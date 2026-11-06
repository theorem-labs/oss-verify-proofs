From Stdlib Require Import ZArith List.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U Require Import Img0.
From OSSVerify.Proofs.omx_clap_core.fuzz_manifest.lib.U.Prog Require Import ManifestModel ManifestMem.
Import ListNotations.
Open Scope Z_scope.

Definition cstr0 (m : word -> option byte) (s : Z) (bs : list byte) : Prop :=
  bytes_at rsegs m s (bs ++ [Z_to_bv 8 0]) /\ Forall (fun b => bv_unsigned b <> 0) bs.

Definition STRLEN : Z := 0x1c6e8.
Definition STRNCMP : Z := 0x1c850.
Definition BCMP : Z := 0x1bfd0.
Definition ISALNUM : Z := 0x143c4.
Definition STRCHR : Z := 0x1c5cc.
Definition STRNCASECMP : Z := 0x1c778.
Definition STRSTR : Z := 0x1c8f4.

Definition STRCHR_K : Z := 32.
Definition STRNCASECMP_K : Z := 48.
Definition STRSTR_K : Z := 2256.

Definition strlen_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs slack : list byte),
    cstr_at m (bv_unsigned a0) bs slack ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0 m []
         (fun r => r = Z_to_bv 64 (Z.of_nat (length bs))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRLEN) fc None m (seg_rom rsegs)).

Definition strncmp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (lb rb : list byte),
    cstr0 m (bv_unsigned a0) lb ->
    cstr0 m (bv_unsigned a1) rb ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0 m []
         (fun r => bv_unsigned r = 0 <->
                   firstn (Z.to_nat (bv_unsigned a2)) (zbytes lb ++ [0])
                   = firstn (Z.to_nat (bv_unsigned a2)) (zbytes rb ++ [0])))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRNCMP) fc None m (seg_rom rsegs)).

Definition bcmp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (lb rb : list byte),
    bytes_at rsegs m (bv_unsigned a0) lb ->
    bytes_at rsegs m (bv_unsigned a1) rb ->
    Z.of_nat (length lb) = bv_unsigned a2 ->
    Z.of_nat (length rb) = bv_unsigned a2 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0 m []
         (fun r => bv_unsigned r = 0 <-> zbytes lb = zbytes rb))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 BCMP) fc None m (seg_rom rsegs)).

Definition isalnum_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z),
    bv_unsigned a0 <= 255 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo 0 m []
         (fun r => bv_unsigned r <> 0 <-> is_alnum (bv_unsigned a0) = true))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ISALNUM) fc None m (seg_rom rsegs)).

Definition strchr_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (bs slack : list byte),
    cstr_at m (bv_unsigned a0) bs slack ->
    1 <= bv_unsigned a1 <= 255 ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + STRCHR_K <= bv_unsigned sp ->
    off_stack sp STRCHR_K (bv_unsigned a0) (Z.of_nat (length bs + 1 + length slack)) ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo STRCHR_K m []
         (fun r => r = match find_idx (fun x => x =? bv_unsigned a1) (zbytes bs) with
                       | Some i => Z_to_bv 64 (bv_unsigned a0 + Z.of_nat i)
                       | None => Z_to_bv 64 0
                       end))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRCHR) fc None m (seg_rom rsegs)).

Definition strncasecmp_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (lb rb : list byte),
    cstr0 m (bv_unsigned a0) lb ->
    cstr0 m (bv_unsigned a1) rb ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + STRNCASECMP_K <= bv_unsigned sp ->
    off_stack sp STRNCASECMP_K (bv_unsigned a0) (Z.of_nat (length lb + 1)) ->
    off_stack sp STRNCASECMP_K (bv_unsigned a1) (Z.of_nat (length rb + 1)) ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo STRNCASECMP_K m []
         (fun r => bv_unsigned r = 0 <->
                   map tolower (firstn (Z.to_nat (bv_unsigned a2)) (zbytes lb ++ [0]))
                   = map tolower (firstn (Z.to_nat (bv_unsigned a2)) (zbytes rb ++ [0]))))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRNCASECMP) fc None m (seg_rom rsegs)).

Definition strstr_contract : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z) (hb hs nb ns : list byte),
    cstr_at m (bv_unsigned a0) hb hs ->
    cstr_at m (bv_unsigned a1) nb ns ->
    nb <> [] -> bv_unsigned a0 <> 0 ->
    bytes_at rsegs m 0x1e368 (le8 (Z_to_bv 64 0x4f978)) -> (exists g, bytes_at rsegs m 0x4f978 (le8 g)) ->
    0x4f978 + 8 <= bv_unsigned sp - STRSTR_K -> 0x1e368 + 8 <= bv_unsigned sp - STRSTR_K ->
    mem_inv rsegs m ->
    stk rsegs m lo (bv_unsigned sp) -> lo + STRSTR_K <= bv_unsigned sp ->
    off_stack sp STRSTR_K (bv_unsigned a0) (Z.of_nat (length hb + 1 + length hs)) ->
    off_stack sp STRSTR_K (bv_unsigned a1) (Z.of_nat (length nb + 1 + length ns)) ->
    evt rsegs
      (kret ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo STRSTR_K m []
         (fun r => r = match find_sub (zbytes hb) (zbytes nb) with
                       | Some i => Z_to_bv 64 (bv_unsigned a0 + Z.of_nat i)
                       | None => Z_to_bv 64 0
                       end))
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 STRSTR) fc None m (seg_rom rsegs)).
