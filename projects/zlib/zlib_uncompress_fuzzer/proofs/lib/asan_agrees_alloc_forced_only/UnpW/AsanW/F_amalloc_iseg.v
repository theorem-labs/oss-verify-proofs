(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Lib Require Import ITree Nodes Decode Arr.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AImg AProto ABase ABytes.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.UnpW.AsanW Require Import AKit AKit2.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.asan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition icptA_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (m : amem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m' (junk1 junk2 : list byte),
    ms' = MS (mkR (Z_to_bv 64 0x5e9a8) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2
                  sp (Z_to_bv 64 n)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 0x5e994) sp (Z_to_bv 64 0) (Z_to_bv 64 1) (Z_to_bv 64 30) a6 a7
                  (Z_to_bv 64 0x5e994) (Z_to_bv 64 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81))
                  s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x5e9ec) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (Z_to_bv 64 (bv_unsigned sp + -2112)); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2112) [CB 2040 junk1]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma icptA_spec : forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 2128 - 16 ->
  mem_inv asegs m ->
  a0 = Z_to_bv 64 n -> 0 <= n < 2^64 ->
  rw_cells asegs m 0xd92d8 [C1 (Z_to_bv 8 1)] ->
  rw_cells asegs m 0xd92fc [C4 (Z_to_bv 64 30)] ->
  rw_cells asegs m 0xcfe08 [C8 (Z_to_bv 64 0x16a128); C8 (Z_to_bv 64 0xd5df8); C8 (Z_to_bv 64 0xd85f8);
                             C8 (Z_to_bv 64 0xd92e8); C8 (Z_to_bv 64 0xd92f0); C8 (Z_to_bv 64 0xd92e0)] ->
  rw_cells asegs m 0x16a14a [C1 (Z_to_bv 8 1)] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (icptA_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e6f0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> NR INI MCS GOT CF34 RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2128 - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  step.                                                          (* [comment removed for export] *)
  carve_frame 2128%nat ST.
  (* [comment removed for export] *)
  cb_split3 FR 16%nat 2040%nat 72%nat. rw_split FR 1%nat FRa FR'. rw_split FR' 1%nat FRt FRs.
  do 8 step.                                                     (* [comment removed for export] *)
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. carve_frame 16%nat ST.
  do 5 step. lstep. step. step. step. if_lit.                    (* [comment removed for export] *)
  do 4 step. release_frame FR ST (bv_unsigned sp + -2128).
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.                             (* [comment removed for export] *)
  step. sstep. step.                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. step. if_lit.                                            (* [comment removed for export] *)
  step. step. step.                                              (* [comment removed for export] *)
  step. step. lstep. step.                                       (* [comment removed for export] *)
  step. step. lstep. step. step.                                 (* [comment removed for export] *)
  step. zstep. zstep. zstep. step.                               (* [comment removed for export] *)
  change ((Z.b2z (30 <? 1) + -1) mod 18446744073709551616) with 18446744073709551615. rewrite land_ones_l by lia.
  sstep.                                                         (* [comment removed for export] *)
  step. if_lit.                                                  (* [comment removed for export] *)
  zstep. zstep. step. step. step. step.                          (* [comment removed for export] *)
  rw_split FRa 1%nat FRa1 FRa2. apply rw_cells_C8_to_C4C4_zero in FRa2. rw_join FRa1 FRa2 FRA.
  apply evtF_done. unfold icptA_post. do 10 eexists. exists (firstn 2040 (skipn 16 junk)). eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  split; [exact FRA|]. split; [exact FRt|]. exact FRs.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition icptB_post (sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0v : word) (F : bvmap 5 word) (fc : bv 32)
    (n lo : Z) (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) (m : amem) : machine_state -> Prop :=
  fun ms' => exists m',
    ms' = MS (mkR (Z_to_bv 64 0x5ea00) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2
                  s0v s1
                  (Z_to_bv 64 AINSTANCE) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 1) (Z_to_bv 64 1) a6 a7
                  s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x3d0fc) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2144)
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [C8 s0v; C8 (Z_to_bv 64 0x5ea00)].

Lemma icptB_spec : forall RNG ra sp gp tp t0 t1 t2 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : amem) (n lo : Z),
  stk asegs m lo (bv_unsigned sp + -2128) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
  mem_inv asegs m ->
  s1 = Z_to_bv 64 n ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (icptB_post sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 sp F fc n lo t0 t1 t2 a6 a7 t3 t4 t5 t6 m)
    (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x5e9f0) fc None m (seg_rom asegs)).
Proof.
  intros until lo. intros ST CEIL LO MI -> RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl [(bv_unsigned sp - 2144, bv_unsigned sp - 2128)]%Z m) as MU. pose proof (wmono_refl asegs m) as WM.
  zstep. zstep. step. step.                                      (* [comment removed for export] *)
  carve_frame 16%nat ST.
  do 3 step.                                                     (* [comment removed for export] *)
  do 7 step.                                                     (* [comment removed for export] *)
  apply evtF_done. unfold icptB_post, AINSTANCE. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|]. exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma icptC_spec : forall RNG sp gp tp t0 t1 t2 s0x s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (rav s0v s1v s2v s3v s4v s5v s0i : word) (F : bvmap 5 word) fc (m : amem) (UB lo : Z) (junk2 : list byte),
  stk asegs m lo (bv_unsigned sp + -2144) -> ATOP <= lo -> lo <= bv_unsigned sp - 2144 ->
  mem_inv asegs m ->
  0 < UB < 2^64 ->
  rw_cells asegs m (bv_unsigned sp + -2144) [C8 s0i; C8 (Z_to_bv 64 0x5ea00)] ->
  (exists csA, rw_cells asegs m (bv_unsigned sp + -2128) csA /\ cells_size csA = 16%nat) ->
  (exists csT, rw_cells asegs m (bv_unsigned sp + -2112) csT /\ cells_size csT = 2040%nat) ->
  rw_cells asegs m (bv_unsigned sp + -72) [C8 sp; CB 8 junk2; C8 s5v; C8 s4v; C8 s3v; C8 s2v; C8 s1v; C8 s0v; C8 rav] ->
  rng_aimg RNG -> rng RNG lo (bv_unsigned sp - lo) ->
  evtF asegs RNG (fun ms' => exists m',
      ms' = MS (mkR rav sp gp tp t0 t1 t2 s0v s1v (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7 s2v s3v s4v s5v s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc rav) fc None m' (seg_rom asegs)
      /\ munch [] m m' /\ wmono asegs m m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp))
    (MS (mkR (Z_to_bv 64 0x3d100) (Z_to_bv 64 (bv_unsigned sp + -2144)) gp tp t0 t1 t2 s0x s1 (Z_to_bv 64 UB) a1 a2 a3 a4 a5 a6 a7
              s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3d100) fc None m (seg_rom asegs)).
Proof.
  intros until junk2. intros ST CEIL LO MI UBR FR16 [csA [FRA SZA]] [csT [FRT SZT]] FRS RIMG RSTK. atop_facts.
  word_range sp SPR.
  pose proof (munch_refl (@nil (Z * Z)) m) as MU. pose proof (wmono_refl asegs m) as WM.
  step. if_cases K0; zify_cond K0. { exfalso. lia. }             (* [comment removed for export] *)
  do 4 step.                                                     (* [comment removed for export] *)
  zstep. do 7 step. zstep. step.                                 (* [comment removed for export] *)
  release_frame FR16 ST (bv_unsigned sp + -2128).
  pose proof (rw_cells_forget asegs _ _ _ FRA) as [jA FRA']. rewrite SZA in FRA'. clear FRA.
  release_frame FRA' ST (bv_unsigned sp + -2112).
  pose proof (rw_cells_forget asegs _ _ _ FRT) as [jT FRT']. rewrite SZT in FRT'. clear FRT.
  release_frame FRT' ST (bv_unsigned sp + -72).
  release_frame FRS ST (bv_unsigned sp).
  apply evtF_done. eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. exact ST.
Qed.
End CANSEC1.
