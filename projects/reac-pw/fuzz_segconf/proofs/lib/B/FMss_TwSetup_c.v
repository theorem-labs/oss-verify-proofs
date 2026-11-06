(* B twin (fm.asan-ubsan, pin ca61e5c9eabc0050) of lib/A/FMss_TwSetup_c.v at cold/port-fm-int 5d8d8a15571, relocated A->B by asan-kit elfmap.py + remap.py over the unstripped twins; every image numeral re-derived by symbol / section (fmb-b4 reloc report). *)
(* lib/A/Prog/TwSetup_c.v (RtStr's port, unchanged from cold/c-asan-rt-fmio-n affce6489c8), stated over the
   local-shadow TW_ASAN and twoway contract (FMss_TwAsan.v, FMss_twoway_strstr_c.v); only the imports differ. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Arr.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import Img0.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Spec Require Import StrStr TwoWay TwSearch.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B.Prog Require Import twoway_strstr_c TwFrame1.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.B Require Import FMss_TwAsan FMss_twoway_strstr_c.
Import ListNotations.
Open Scope Z_scope.

Definition TW_STATIC (sp a0 a1 : word) (m0 : word -> option byte) (hb hs nb : list byte) (lo : Z) (g : word) : Prop :=
  stk rsegs m0 lo (bv_unsigned sp) /\ lo + 4560 <= bv_unsigned sp /\
  bytes_at rsegs m0 (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs) /\ ~ In (Z_to_bv 8 0) hb /\
  (- (bv_unsigned a0 + Z.of_nat (length hb) + 1)) mod 8 <= Z.of_nat (length hs) /\
  bytes_at rsegs m0 (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) nb /\ nb <> [] /\
  mem_inv rsegs m0 /\
  (bv_unsigned a0 + Z.of_nat (length hb) + 1 + Z.of_nat (length hs) <= bv_unsigned sp - 4560
     \/ bv_unsigned sp <= bv_unsigned a0) /\
  (bv_unsigned a1 + Z.of_nat (length nb) + 1 <= bv_unsigned sp - 4560 \/ bv_unsigned sp <= bv_unsigned a1) /\
  bytes_at rsegs m0 GOT_GUARD (le8 (Z_to_bv 64 GUARD)) /\ bytes_at rsegs m0 GUARD (le8 g) /\
  GUARD + 8 <= bv_unsigned sp - 4560 /\ GOT_GUARD + 8 <= bv_unsigned sp - 4560 /\
  TW_ASAN sp a0 a1 m0 hb nb lo.

Definition AT918 (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 : word) (F : bvmap 5 word) (fc : bv 32)
    (m0 : word -> option byte) (hb hs nb : list byte) (lo : Z) (g : word) : Prop :=
  forall (m : word -> option byte) (j48 : list byte) (bset tbl : list word) (x5 x6 x7 x16 x17 x28 x29 x30 x31 : word),
    rw_cells rsegs m (bv_unsigned sp + -2240) [CB 48 j48] ->
    u64arr rsegs m (bv_unsigned sp + -2192) tbl -> TBL (map bv_unsigned nb) tbl ->
    u64arr rsegs m (bv_unsigned sp + -144) bset -> BSET (map bv_unsigned nb) bset ->
    rw_cells rsegs m (bv_unsigned sp + -112)
      [C8 g; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk rsegs m lo (bv_unsigned sp + -2240) -> mem_inv rsegs m ->
    munch [(bv_unsigned sp - 4560, bv_unsigned sp)] m0 m -> wmono rsegs m0 m ->
    bytes_at rsegs m (bv_unsigned a0) (hb ++ Z_to_bv 8 0 :: hs) ->
    bytes_at rsegs m (bv_unsigned a1) (nb ++ [Z_to_bv 8 0]) ->
    bytes_at rsegs m GOT_GUARD (le8 (Z_to_bv 64 GUARD)) -> bytes_at rsegs m GUARD (le8 g) ->
    (length nb <= length hb)%nat ->
    evt rsegs (twoway_strstr_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 hb hs nb lo m0)
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2240)) gp tp x5 x6 x7 a1 a0
               (Z_to_bv 64 (-1)) (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -144))
               (Z_to_bv 64 (bv_unsigned sp + -2192)) (Z_to_bv 64 (Z.of_nat (length nb))) x16 x17
               s2 (Z_to_bv 64 GUARD) s4 s5 (Z_to_bv 64 (bv_unsigned a1 + 1)) (Z_to_bv 64 (Z.of_nat (length nb)))
               s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x9ba7c) fc None m (seg_rom rsegs)).

Definition TW_FRONT : Prop :=
  (forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m0 hb hs nb lo g,
     TW_STATIC sp a0 a1 m0 hb hs nb lo g ->
     AT918 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m0 hb hs nb lo g) ->
  twoway_strstr_contract.

Definition TW_BACK : Prop :=
  forall ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m0 hb hs nb lo g,
    TW_STATIC sp a0 a1 m0 hb hs nb lo g ->
    AT918 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 a0 a1 F fc m0 hb hs nb lo g.
