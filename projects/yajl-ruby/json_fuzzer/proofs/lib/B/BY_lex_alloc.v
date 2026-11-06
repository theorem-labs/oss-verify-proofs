(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep SFW1_lemmas.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BI_shadow BI_asan_memset BYajlRep BYajl_iface BY_rz.
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
Definition ALEXA_MAL_RET : Z := 0x82cb8.
Definition ALEXA_BA_RET : Z := 0x82cd8.   (* [comment removed for export] *)

End RC__1.

Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
(* [comment removed for export] *)
Definition alexa_frame (m : mem) (SQ : Z) (ra s0 s1 s2 s3 s4 : word) : Prop :=
  rw_cells bsegs m SQ [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

(* [comment removed for export] *)
Lemma alexa1_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (AF aC v8 lo HB HN : Z) (shbH : list byte),
  stk bsegs m1 lo (bv_unsigned sp) -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  rw_cells bsegs m1 677280 [C8 (Z_to_bv 64 714168)] -> rw_cells bsegs m1 714168 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells bsegs m1 AF [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  u8arr bsegs m1 (2147450880 + HB / 8) shbH -> shbH = blk_shadow HN -> HB <= AF -> AF + 32 <= HB + 8 * (HN / 8) -> AF mod 8 = 0 ->
  0 < HB -> HB mod 16 = 0 -> HB + HN <= alloc_ceiling -> 17594333495296 <= HB ->
  0 <= aC < 2^64 -> 0 <= v8 < 2^64 ->
  pol P lo (bv_unsigned sp) -> pol P 0x10000 0x603000 -> pol P AF (AF + 32) -> pol P (2147450880 + HB / 8) (2147450880 + HB / 8 + (HN + 7) / 8) ->
  evtA bsegs P (fun ms' => exists (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 ALEXA_MAL_RET) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 AF) (Z_to_bv 64 v8) (Z_to_bv 64 0) (Z_to_bv 64 48) (Z_to_bv 64 AY_MALLOC_W) a3 a4 a5 a6 a7
                   (Z_to_bv 64 aC) s3 (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AY_MALLOC_W) fc None m' (seg_rom bsegs)
      /\ munch [(bv_unsigned sp + -48, bv_unsigned sp)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -48) /\ alexa_frame m' (bv_unsigned sp + -48) ra s0 s1 s2 s3 s4)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 AF) (Z_to_bv 64 aC) (Z_to_bv 64 v8) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_LEX_ALLOC) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until shbH. intros ST MI CEIL' LOQ SPH G1 G2 YAF HBS HBSeq HB1 HB2 AF8 HB0 HB16 HBHI HBS2 ACR V8R PSTK PIMG PHB PHBS.
  unfold AY_LEX_ALLOC, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W, ALEXA_MAL_RET, pol in *.
  pose proof (blk_shadow_length HN ltac:(lia)) as HBSlen. rewrite <- HBSeq in HBSlen.
  pose proof (munch_refl [(bv_unsigned sp + -48, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  yhide YAF. yhide HBS. yhide PHB. yhide PHBS. yhide PIMG. yhide G1. yhide G2.
  carve_frame 48%nat ST.
  stepA. apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  do 6 stepA.                                         (* [comment removed for export] *)
  ugd.                                                (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  zstepA. ugd.                                        (* [comment removed for export] *)
  yreveal G1 MU WM. yreveal G2 MU WM. yshow PIMG.
  do 3 stepA.                                         (* [comment removed for export] *)
  clear G1 G2. yhide PIMG. yreveal YAF MU WM. yreveal HBS MU WM. yshow PHB. yshow PHBS. yhide FR. yhide PSTK.
  shadow_fast HBS AF 8.                               (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  shadow_fast HBS (AF + 24) 8.                        (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  zstepA. zstepA. stepA.                              (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  yshow FR.
  apply evtA_done. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption| exact FR].
Qed.

(* [comment removed for export] *)
Lemma alexa2_seg : forall (P : acc -> Prop) (gp tp t0 t1 t2 s3v a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (AF aC v8 lo SQ Lx : Z) (junk ws : list byte),
  stk bsegs m1 lo SQ -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo + 2128 <= SQ -> SQ + 48 <= 2^47 ->
  rw_cells bsegs m1 Lx [CB 48 junk] -> icp_globals bsegs m1 2147450880 ->
  shadow_window bsegs m1 2147450880 Lx 48 ws -> range_clean 2147450880 Lx 48 ws ->
  0 < Lx -> Lx + 48 <= alloc_ceiling -> 17594333495296 <= Lx -> 0 <= AF < 2^64 ->
  pol P (SQ - 2128) SQ -> pol P 0x10000 0x603000 -> pol P Lx (Lx + 48) -> pol P (shw_lo 2147450880 Lx) (shw_hi 2147450880 Lx 48) ->
  evtA bsegs P (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 ALEXA_BA_RET) (Z_to_bv 64 SQ) gp tp t0' t1' t2' (Z_to_bv 64 AF) (Z_to_bv 64 v8) (Z_to_bv 64 AF) a1' a2' a3' a4' a5' a6' a7'
                   (Z_to_bv 64 aC) (Z_to_bv 64 Lx) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (Z_to_bv 64 AY_BUF_ALLOC) fc None m' (seg_rom bsegs)
      /\ munch [(SQ - 2128, SQ); (Lx, Lx + 48)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo SQ /\ rw_cells bsegs m' Lx [CB 48 (repeat (Z_to_bv 8 0) 48)])
    (MS (mkR (Z_to_bv 64 ALEXA_MAL_RET) (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 AF) (Z_to_bv 64 v8) (Z_to_bv 64 Lx) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 aC) s3v (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ALEXA_MAL_RET) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until ws. intros ST MI CEIL' LOQ SQH NEW IG SW RC L0 LHI LSH AFR PSTK PIMG PL PWL.
  unfold ALEXA_MAL_RET, ALEXA_BA_RET, AY_BUF_ALLOC, pol in *.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof (shw_geom 2147450880 Lx 48 ltac:(lia) ltac:(lia) ltac:(lia)) as GEO. cbv zeta in GEO.
  pose proof (munch_refl [(SQ - 2128, SQ); (Lx, Lx + 48)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  stepA.                                                (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1. { kill K1. }       (* [comment removed for export] *)
  stepA. stepA. stepA.                                  (* [comment removed for export] *)
  stepA.                                                (* [comment removed for export] *)
  call_spA (asan_memset_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Lx 0 48 2147450880 ws junk lo).
  all: rewrite ?USQ.
  - exact ST.
  - aceil; lia.
  - lia.
  - exact MI.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - lia.
  - lia.
  - lia.
  - left. lia.
  - right. lia.
  - exact NEW.
  - exact IG.
  - exact SW.
  - exact RC.
  - left. lia.
  - exact PSTK.
  - exact PIMG.
  - exact PL.
  - exact PWL.
  - stepA.                                              (* [comment removed for export] *)
    stepA.                                              (* [comment removed for export] *)
    lazymatch goal with H : stk bsegs _ lo (bv_unsigned _) |- _ => rewrite USQ in H | _ => idtac end.
    finishA.
Qed.

(* [comment removed for export] *)
Lemma alexa3_seg : forall (P : acc -> Prop) (gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0o s1o s2o s3o s4o : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (AF aC v8 lo SQ Lx B0 : Z) (shbL : list byte),
  stk bsegs m1 lo SQ -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo <= SQ -> SQ + 48 <= 2^47 ->
  alexa_frame m1 SQ rav s0o s1o s2o s3o s4o ->
  rw_cells bsegs m1 Lx [CB 48 (repeat (Z_to_bv 8 0) 48)] -> u8arr bsegs m1 (2147450880 + Lx / 8) shbL -> shbL = blk_shadow 48 ->
  0 < Lx -> Lx mod 16 = 0 -> Lx + 48 <= alloc_ceiling -> 17594333495296 <= Lx ->
  0 <= aC < 2^31 -> 0 <= v8 < 2^31 -> 0 <= AF < 2^64 -> 0 <= B0 < 2^64 ->
  pol P lo (SQ + 48) -> pol P Lx (Lx + 48) -> pol P (2147450880 + Lx / 8) (2147450880 + Lx / 8 + 6) ->
  evtA bsegs P (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR rav (Z_to_bv 64 (SQ + 48)) gp tp t0' t1' t2' s0o s1o (Z_to_bv 64 Lx) a1' a2' a3' a4' a5' a6' a7' s2o s3o s4o s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc rav) fc None m' (seg_rom bsegs)
      /\ munch [(Lx, Lx + 48)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (SQ + 48)
      /\ rw_cells bsegs m' Lx [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 B0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0);
                              C4 (Z_to_bv 64 aC); C4 (Z_to_bv 64 v8); C8 (Z_to_bv 64 AF)])
    (MS (mkR (Z_to_bv 64 ALEXA_BA_RET) (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 AF) (Z_to_bv 64 v8) (Z_to_bv 64 B0) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 aC) (Z_to_bv 64 Lx) (Z_to_bv 64 2147450880) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 ALEXA_BA_RET) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until shbL.
  intros ST MI CEIL' LOQ SQH FR LXC LS LSeq L0 L16 LHI LSH ACR V8R AFR B0R PSTK PL PLS.
  unfold ALEXA_BA_RET, alexa_frame, pol in *.
  pose proof (blk_shadow_length 48 ltac:(lia)) as LSlen. rewrite <- LSeq in LSlen.
  assert (L8 : Lx mod 8 = 0) by lia.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(Lx, Lx + 48)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB bsegs _ _ [] 48 _ [] [4;4;4;4;8;4;4;4;4;8]%nat) in LXC; [| reflexivity]. cbn [app mk_CB_cells firstn skipn repeat] in LXC.
  yhide FR.
  zstepA. ugd.                                        (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  shadow_fast LS (Lx + 16) 8.                         (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  zstepA. shadow_fast LS (Lx + 32) 4. zstepA.          (* [comment removed for export] *)
  zstepA. shadow_fast LS (Lx + 36) 4. zstepA.          (* [comment removed for export] *)
  zstepA. shadow_fast LS (Lx + 40) 8. zstepA.          (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  yreveal FR MU WM.
  do 7 stepA.                                         (* [comment removed for export] *)
  lazymatch goal with H : stk bsegs ?mx lo SQ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2 | _ => idtac end.
  release_frame FR ST2 (SQ + 48).
  stepA.                                              (* [comment removed for export] *)
  apply evtA_done. do 14 eexists. eexists _. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [assumption|].
  lazymatch goal with H : rw_cells bsegs _ Lx _ |- _ => eapply rw_cells_recast; [exact H| cbn; repeat split; reflexivity| reflexivity| reflexivity] end.
Qed.
End RC__2.
