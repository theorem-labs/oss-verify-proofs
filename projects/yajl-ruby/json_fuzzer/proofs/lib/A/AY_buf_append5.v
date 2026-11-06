(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlLeaf YajlBuf YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AYajlRep AYajl_iface AY_rz AY_buf_append1 AY_buf_append2 AY_buf_append3 AY_buf_append4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac aceil := first [pose proof alloc_ceiling_range as CEILB | idtac].
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition AAPP_MAL_RET : Z := 0x86ac4.

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; lia.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition aframe13 (m : mem) (SQ : Z) (junk : list byte) (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) : Prop :=
  rw_cells asegs m SQ [CB 24 junk; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition amain1_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m1 : mem)
    (B D S nz AF st len used lo : Z) : machine_state -> Prop :=
  fun ms' => exists (junk : list byte) (m' : mem),
    aframe13 m' (bv_unsigned sp + -128) junk ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
    /\ stk asegs m' lo (bv_unsigned sp + -128) /\ munch [(bv_unsigned sp + -128, bv_unsigned sp); (B + 4, B + 8)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
    /\ ( (st <> 0 /\ rw_cells asegs m' B [C4 (Z_to_bv 64 st); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 used); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 AF)]
          /\ exists x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
             ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 AAPP_EPILOGUE) fc None m' (seg_rom asegs))
      \/ (st = 0 /\ D <> 0 /\ nz = 0 /\ rw_cells asegs m' B [C4 (Z_to_bv 64 st); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 used); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 AF)]
          /\ exists x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
             ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                      F (Z_to_bv 64 AAPP_EPILOGUE) fc None m' (seg_rom asegs))
      \/ (st = 0 /\ D <> 0 /\ nz <> 0 /\ rw_cells asegs m' B [C4 (Z_to_bv 64 st); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 used); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 AF)]
          /\ exists x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
             ms' = MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (Z_to_bv 64 (B + 16)) (Z_to_bv 64 B) x10 x11 x12 x13 x14 x15 x16 x17
                           s2 (Z_to_bv 64 nz) (Z_to_bv 64 S) s5 s6 s7 (Z_to_bv 64 2147450880) (Z_to_bv 64 ((B + 16) / 8 + 2147450880)) s10 (Z_to_bv 64 (B / 8 + 2147450880)) x28 x29 x30 x31)
                      F (Z_to_bv 64 AAPP_SIZE) fc None m' (seg_rom asegs))
      \/ (st = 0 /\ D = 0 /\ rw_cells asegs m' B [C4 (Z_to_bv 64 st); C4 (Z_to_bv 64 2048); C4 (Z_to_bv 64 used); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 AF)]
          /\ exists x5 x6 x7 x13 x14 x15 x16 x17 x28 x29 x30 x31,
             ms' = MS (mkR (Z_to_bv 64 AAPP_MAL_RET) (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (Z_to_bv 64 (B + 16)) (Z_to_bv 64 B)
                           (Z_to_bv 64 0) (Z_to_bv 64 2048) (Z_to_bv 64 AY_MALLOC_W) x13 x14 x15 x16 x17
                           (Z_to_bv 64 (B + 4)) (Z_to_bv 64 nz) (Z_to_bv 64 S) (Z_to_bv 64 (B + 24)) (Z_to_bv 64 ((B + 4) / 8 + 2147450880)) (Z_to_bv 64 ((B + 24) / 8 + 2147450880))
                           (Z_to_bv 64 2147450880) (Z_to_bv 64 ((B + 16) / 8 + 2147450880)) s10 (Z_to_bv 64 (B / 8 + 2147450880)) x28 x29 x30 x31)
                      F (Z_to_bv 64 AY_MALLOC_W) fc None m' (seg_rom asegs)) ).

Lemma amain1_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem)
    (B D S nz AF st len used lo : Z) (shbB shbH : list byte) (HB HN : Z),
  stk asegs m1 lo (bv_unsigned sp) -> mem_inv asegs m1 -> alloc_ceiling <= lo -> lo + 8320 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m1 B [C4 (Z_to_bv 64 st); C4 (Z_to_bv 64 len); C4 (Z_to_bv 64 used); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D); C8 (Z_to_bv 64 AF)] ->
  u8arr asegs m1 (2147450880 + B / 8) shbB -> shbB = blk_shadow 32 ->
  rw_cells asegs m1 674224 [C8 (Z_to_bv 64 711544)] -> rw_cells asegs m1 711544 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells asegs m1 AF [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  u8arr asegs m1 (2147450880 + HB / 8) shbH -> shbH = blk_shadow HN -> HB <= AF -> AF + 32 <= HB + 8 * (HN / 8) -> AF mod 8 = 0 ->
  0 < HB -> HB mod 16 = 0 -> HB + HN <= alloc_ceiling -> 17594333495296 <= HB -> (HB + HN <= B \/ B + 32 <= HB) ->
  0 < B -> B mod 16 = 0 -> B + 32 <= alloc_ceiling -> 17594333495296 <= B ->
  0 <= st < 2^31 -> 0 <= len < 2^31 -> 0 <= used < 2^31 -> 0 <= D < 2^64 -> 0 <= nz < 2^64 -> 0 <= S < 2^64 ->
  pol P lo (bv_unsigned sp) -> pol P 0x10000 0x603000 -> pol P B (B + 32) -> pol P (2147450880 + B / 8) (2147450880 + B / 8 + 4) ->
  pol P AF (AF + 32) -> pol P (2147450880 + HB / 8) (2147450880 + HB / 8 + (HN + 7) / 8) ->
  evtA asegs P (amain1_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m1 B D S nz AF st len used lo)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 B) (Z_to_bv 64 S) (Z_to_bv 64 nz) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AY_BUF_APPEND) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until HN.
  intros ST MI CEIL' LOQ SPH BC BSH BSHeq G1 G2 YAF HBS HBSeq HB1 HB2 AF8 HB0 HB16 HBHI HBS2 SBH B0 B16 BHI BSH2 STR RL RU DR NZR SR.
  intros PSTK PIMG PB PBS PHB PHBS.
  unfold AY_BUF_APPEND, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W in *. unfold pol in PSTK, PIMG, PB, PBS, PHB, PHBS.
  pose proof (blk_shadow_length 32 ltac:(lia)) as BSHlen. rewrite <- BSHeq in BSHlen.
  pose proof (blk_shadow_length HN ltac:(lia)) as HBSlen. rewrite <- HBSeq in HBSlen.
  assert (B8 : B mod 8 = 0) by lia.
  pose proof (munch_refl [(bv_unsigned sp + -128, bv_unsigned sp); (B + 4, B + 8)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  (* [comment removed for export] *)
  yhide BSH. yhide G1. yhide G2. yhide YAF. yhide HBS. yhide PIMG. yhide PB. yhide PBS. yhide PHB. yhide PHBS. yhide SBH.
  carve_frame 128%nat ST.
  stepA.                                                                            (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [] 128 _ [] [24;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  do 13 stepA.                                                                      (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { kill K0. }                                   (* [comment removed for export] *)
  stepA. stepA. stepA.                                                              (* [comment removed for export] *)
  yreveal G1 MU WM. yreveal G2 MU WM. yreveal BSH MU WM. yshow PIMG. yshow PB. yshow PBS. yhide PSTK.
  stepA. zstepA. zstepA.                                                            (* [comment removed for export] *)
  clear G1 G2. yhide PIMG.
  shadow_fast BSH B 4.                                                              (* [comment removed for export] *)
  zstepA. rewrite ysx32_small by lia.                                               (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1.                                                (* [comment removed for export] *)
  2:{ (* [comment removed for export] *)
      assert (STNZ : st <> 0) by (revert K1; rewrite ?unsigned_lit by lia; lia).
      unfold amain1_post, aframe13, AAPP_EPILOGUE. apply evtA_done. eexists _, _.
      split; [exact FR|]. split; [assumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
      left. split; [exact STNZ|]. split; [exact BC|]. repeat eexists. }
  assert (STZ : st = 0) by (revert K1; rewrite ?unsigned_lit by lia; lia).
  zstepA.                                                                           (* [comment removed for export] *)
  shadow_fast BSH (B + 16) 8.                                                       (* [comment removed for export] *)
  zstepA.                                                                           (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2.                                                (* [comment removed for export] *)
  2:{ (* [comment removed for export] *)
      assert (DNZ : D <> 0) by (revert K2; rewrite ?unsigned_lit by lia; lia).
      zstepA. if_cases K3; zify_cond K3.                                            (* [comment removed for export] *)
      - assert (NZ0 : nz = 0) by (revert K3; rewrite ?unsigned_lit by lia; lia).
        unfold amain1_post, aframe13, AAPP_EPILOGUE. apply evtA_done. eexists _, _.
        split; [exact FR|]. split; [assumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
        right; left. split; [exact STZ|]. split; [exact DNZ|]. split; [exact NZ0|]. split; [exact BC|]. repeat eexists.
      - assert (NZ1 : nz <> 0) by (revert K3; rewrite ?unsigned_lit by lia; lia).
        stepA.                                                                        (* [comment removed for export] *)
        unfold amain1_post, aframe13, AAPP_SIZE. apply evtA_done. eexists _, _.
        split; [exact FR|]. split; [assumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
        right; right; left. split; [exact STZ|]. split; [exact DNZ|]. split; [exact NZ1|]. split; [exact BC|]. repeat eexists. }
  (* [comment removed for export] *)
  assert (DZ : D = 0) by (revert K2; rewrite ?unsigned_lit by lia; lia).
  zstepA.                                                                           (* [comment removed for export] *)
  shadow_fast BSH (B + 4) 4.                                                        (* [comment removed for export] *)
  stepA. zstepA. zstepA.                                                            (* [comment removed for export] *)
  zstepA. shadow_addr.                                                              (* [comment removed for export] *)
  zstepA.                                                                           (* [comment removed for export] *)
  zstepA.                                                                           (* [comment removed for export] *)
  shadow_at BSH (B + 24) 8. shadow_ld. zstepA. if_false.                          (* [comment removed for export] *)
  zstepA.                                                                           (* [comment removed for export] *)
  yshow PHB. yshow PHBS. yshow SBH.
  unfold yhide in YAF. eapply (rw_cells_transport asegs) in YAF; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length]; lia].
  unfold yhide in HBS. eapply (u8arr_transport asegs) in HBS; [| exact MU| exact WM| cbv [disjoint_from fst snd]; lia].
  yhide SBH.
  shadow_fast HBS AF 8.                                                             (* [comment removed for export] *)
  zstepA. shadow_fast HBS (AF + 24) 8.                                              (* [comment removed for export] *)
  zstepA. zstepA.                                                                   (* [comment removed for export] *)
  stepA. zstepA.                                                                    (* [comment removed for export] *)
  stepA.                                                                            (* [comment removed for export] *)
  unfold amain1_post, aframe13, AAPP_MAL_RET. apply evtA_done. eexists _, _.
  split; [exact FR|]. split; [assumption|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  right; right; right. split; [exact STZ|]. split; [exact DZ|]. split; [exact BC|]. repeat eexists.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma amain2_seg : forall (P : acc -> Prop) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s10v t3 t4 t5 t6 : word)
    (F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem)
    (B B0 S nz AF used SQ sh6 sh7 sh9 sh11 : Z) (shbB shb0 junk0 : list byte),
  mem_inv asegs m1 ->
  rw_cells asegs m1 B [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2048); C4 (Z_to_bv 64 used); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 AF)] ->
  u8arr asegs m1 (2147450880 + B / 8) shbB -> shbB = blk_shadow 32 ->
  rw_cells asegs m1 B0 [CB 2048 junk0] -> u8arr asegs m1 (2147450880 + B0 / 8) shb0 -> shb0 = blk_shadow 2048 ->
  0 < B -> B mod 16 = 0 -> B + 32 <= alloc_ceiling -> 17594333495296 <= B ->
  0 < B0 -> B0 mod 16 = 0 -> B0 + 2048 <= alloc_ceiling -> 17594333495296 <= B0 -> (B + 32 <= B0 \/ B0 + 2048 <= B) ->
  0 <= used < 2^31 -> 0 <= nz < 2^64 ->
  sh6 = 2147450880 + (B + 4) / 8 -> sh7 = 2147450880 + (B + 24) / 8 -> sh9 = 2147450880 + (B + 16) / 8 -> sh11 = 2147450880 + B / 8 ->
  pol P B (B + 32) -> pol P (2147450880 + B / 8) (2147450880 + B / 8 + 4) ->
  pol P B0 (B0 + 2048) -> pol P (2147450880 + B0 / 8) (2147450880 + B0 / 8 + 256) ->
  evtA asegs P (fun ms' => exists (m' : mem),
      munch [(B, B + 32); (B0, B0 + 1)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ rw_cells asegs m' B [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 2048); C4 (Z_to_bv 64 used); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 B0); C8 (Z_to_bv 64 AF)]
      /\ rw_cells asegs m' B0 [CB 0 []; C1 (Z_to_bv 8 0); CB 2047 (skipn 1 junk0)]
      /\ ( (nz = 0 /\ exists x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
              ms' = MS (mkR x1 (Z_to_bv 64 SQ) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
                       F1 (Z_to_bv 64 AAPP_EPILOGUE) fc1 None m' (seg_rom asegs))
         \/ (nz <> 0 /\ exists x10 x11,
              ms' = MS (mkR (Z_to_bv 64 AAPP_MAL_RET) (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 (B + 16)) (Z_to_bv 64 B) x10 x11 a2 a3 a4 a5 a6 a7
                            (Z_to_bv 64 (B + 4)) (Z_to_bv 64 nz) (Z_to_bv 64 S) (Z_to_bv 64 (B + 24)) (Z_to_bv 64 sh6) (Z_to_bv 64 sh7)
                            (Z_to_bv 64 2147450880) (Z_to_bv 64 sh9) s10v (Z_to_bv 64 sh11) t3 t4 t5 t6)
                       F1 (Z_to_bv 64 AAPP_SIZE) fc1 None m' (seg_rom asegs)) ))
    (MS (mkR (Z_to_bv 64 AAPP_MAL_RET) (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 (B + 16)) (Z_to_bv 64 B) (Z_to_bv 64 B0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 (B + 4)) (Z_to_bv 64 nz) (Z_to_bv 64 S) (Z_to_bv 64 (B + 24)) (Z_to_bv 64 sh6) (Z_to_bv 64 sh7)
             (Z_to_bv 64 2147450880) (Z_to_bv 64 sh9) s10v (Z_to_bv 64 sh11) t3 t4 t5 t6)
        F1 (Z_to_bv 64 AAPP_MAL_RET) fc1 None m1 (seg_rom asegs)).
Proof. aceil.
  intros until junk0. intros MI BC BSH BSHeq NEW B0S B0Seq Bp B16 BHI BSH2 B0p B016 B0HI B0SH2 SB0 RU NZR E6 E7 E9 E11 PB PBS PD PDS.
  unfold AAPP_MAL_RET in *. unfold pol in PB, PBS, PD, PDS.
  pose proof (blk_shadow_length 32 ltac:(lia)) as BSHlen. rewrite <- BSHeq in BSHlen.
  pose proof (blk_shadow_length 2048 ltac:(lia)) as B0Slen. rewrite <- B0Seq in B0Slen.
  assert (B8 : B mod 8 = 0) by lia. assert (B08 : B0 mod 8 = 0) by lia.
  pose proof (proj1 (proj1 NEW)) as WF0. cbn [cells_wf cell_wf] in WF0. destruct WF0 as [LJ0 _].
  pose proof (munch_refl [(B, B + 32); (B0, B0 + 1)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  shadow_at BSH (B + 16) 8. shadow_ld. zstepA. if_false.                          (* [comment removed for export] *)
  zstepA.                                                                           (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { kill K1. }                                   (* [comment removed for export] *)
  shadow_fast B0S B0 1.                                                             (* [comment removed for export] *)
  apply (rw_cells_split_CB asegs _ _ [] 2048 _ [] [1; 2047]%nat) in NEW; [| reflexivity]. cbn [app mk_CB_cells] in NEW.
  zstepA.                                                                           (* [comment removed for export] *)
  zstepA. if_cases K2; zify_cond K2.                                                (* [comment removed for export] *)
  - assert (NZ0 : nz = 0) by (revert K2; rewrite ?unsigned_lit by lia; lia).
    unfold AAPP_EPILOGUE. apply evtA_done. eexists _. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact BC|]. split.
    + eapply rw_cells_recast; [exact NEW| cbn; rewrite length_skipn, LJ0; repeat split; lia| cbn [cells_bytes cbytes app]; rewrite firstn_all2 by (rewrite length_skipn; lia); reflexivity| reflexivity].
    + left. split; [exact NZ0|]. repeat eexists.
  - assert (NZ1 : nz <> 0) by (revert K2; rewrite ?unsigned_lit by lia; lia).
    unfold AAPP_SIZE. apply evtA_done. eexists _. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact BC|]. split.
    + eapply rw_cells_recast; [exact NEW| cbn; rewrite length_skipn, LJ0; repeat split; lia| cbn [cells_bytes cbytes app]; rewrite firstn_all2 by (rewrite length_skipn; lia); reflexivity| reflexivity].
    + right. split; [exact NZ1|]. repeat eexists.
Qed.

(* [comment removed for export] *)
End RC__2.
