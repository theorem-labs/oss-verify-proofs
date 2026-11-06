(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import ShapeAlgCfg.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AYajlRep AYajl_iface AY_acct_needs AY_rz AY_hand.
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
Definition AYF_RET1 : Z := 0x82b08.   (* [comment removed for export] *)
Definition AYF_RET2 : Z := 0x82b24.   (* [comment removed for export] *)
Definition AYF_RET3 : Z := 0x82b40.   (* [comment removed for export] *)

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition ahcells (cb cx L : Z) (pew : word) (bc : Z) (pad : word) (D SBK SZ U H : Z) : list cell :=
  [C8 (Z_to_bv 64 cb); C8 (Z_to_bv 64 cx); C8 (Z_to_bv 64 L); C8 pew; C4 (Z_to_bv 64 bc); C4 pad; C8 (Z_to_bv 64 D);
   C8 (Z_to_bv 64 SBK); C4 (Z_to_bv 64 SZ); C4 (Z_to_bv 64 U); C8 (Z_to_bv 64 (H + 72));
   C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ayf1_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (H lo cb cx L bc D SBK SZ U : Z) (pew pad : word) (shbH : list byte),
  stk asegs m1 lo (bv_unsigned sp) -> mem_inv asegs m1 -> alloc_ceiling <= lo -> lo + 32 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  rw_cells asegs m1 H (ahcells cb cx L pew bc pad D SBK SZ U H) ->
  u8arr asegs m1 (2147450880 + H / 8) shbH -> shbH = blk_shadow 104 ->
  rw_cells asegs m1 674224 [C8 (Z_to_bv 64 711544)] -> rw_cells asegs m1 711544 [C8 (Z_to_bv 64 2147450880)] ->
  0 < H -> H mod 16 = 0 -> H + 104 <= alloc_ceiling -> 17594333495296 <= H -> 0 <= SBK < 2^64 ->
  pol P lo (bv_unsigned sp) -> pol P 0x10000 0x603000 -> pol P H (H + 104) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) ->
  evtA asegs P (fun ms' => exists (a0' a1' a2' : word) (junk : list byte) (m' : mem),
      munch [(bv_unsigned sp + -32, bv_unsigned sp)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo (bv_unsigned sp + -32) /\ rw_cells asegs m' (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra]
      /\ ((SBK = 0 /\ ms' = MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 H) (Z_to_bv 64 2147450880) a0' a1' a2' a3 a4 a5 a6 a7
                                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AYF_RET1) fc None m' (seg_rom asegs))
          \/ (SBK <> 0 /\ ms' = MS (mkR (Z_to_bv 64 AYF_RET1) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 H) (Z_to_bv 64 2147450880)
                                          (Z_to_bv 64 0) (Z_to_bv 64 SBK) (Z_to_bv 64 AY_FREE_W) (Z_to_bv 64 0) a4 a5 a6 a7
                                       s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_FREE_W) fc None m' (seg_rom asegs))))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 H) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_FREE) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until shbH. intros ST MI CEIL' LOQ SPH HC HS HSeq G1 G2 H0 H16 HHI HSH SBR PSTK PIMG PH PHS.
  unfold ahcells in *. unfold AY_FREE, AY_FREE_W, AY_MALLOC_W, AY_REALLOC_W, AYF_RET1, pol in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as HSlen. rewrite <- HSeq in HSlen.
  assert (H8 : H mod 8 = 0) by lia.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (munch_refl [(bv_unsigned sp + -32, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  carve_frame 32%nat ST.
  stepA. apply (rw_cells_split_CB asegs _ _ [] 32 _ [] [8;8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  stepA. stepA. stepA.                                (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { kill K0. }     (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  do 3 stepA.                                         (* [comment removed for export] *)
  zstepA. shadow_fast HS (H + 48) 8.                  (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1.                  (* [comment removed for export] *)
  - (* [comment removed for export] *)
    apply evtA_done. eexists _, _, _, _, _. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FR|].
    left. split; [revert K1; rewrite ?unsigned_lit by lia; intros K1; lia| reflexivity].
  - zstepA. shadow_fast HS (H + 64) 8.                (* [comment removed for export] *)
    zstepA.                                           (* [comment removed for export] *)
    zstepA. shadow_fast HS (H + 88) 8.                (* [comment removed for export] *)
    zstepA. shadow_fast HS (H + 96) 8.                (* [comment removed for export] *)
    zstepA. zstepA.                                   (* [comment removed for export] *)
    stepA.                                            (* [comment removed for export] *)
    apply evtA_done. eexists (Z_to_bv 64 0), (Z_to_bv 64 0), (Z_to_bv 64 0), _, _. split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. split; [exact FR|].
    right. split; [revert K1; rewrite ?unsigned_lit by lia; intros K1; lia| reflexivity].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ayf2_seg : forall (P : acc -> Prop) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (H SQ cb cx L bc D SBK SZ U : Z) (pew pad : word) (shbH : list byte),
  mem_inv asegs m1 -> 0 <= SQ < 2^47 ->
  rw_cells asegs m1 H (ahcells cb cx L pew bc pad D SBK SZ U H) ->
  u8arr asegs m1 (2147450880 + H / 8) shbH -> shbH = blk_shadow 104 ->
  0 < H -> H mod 16 = 0 -> H + 104 <= alloc_ceiling -> 17594333495296 <= H -> 0 <= D < 2^64 ->
  pol P H (H + 104) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) ->
  evtA asegs P (fun ms' => exists (a1' : word),
      ms' = MS (mkR (Z_to_bv 64 AYF_RET2) (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 H) (Z_to_bv 64 2147450880) (Z_to_bv 64 D) a1' a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_BUF_FREE) fc None m1 (seg_rom asegs))
    (MS (mkR ra (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 H) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AYF_RET1) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until shbH. intros MI SQR HC HS HSeq H0 H16 HHI HSH DR PH PHS.
  unfold ahcells in *. unfold AYF_RET1, AYF_RET2, AY_BUF_FREE, AY_FREE_W, AY_MALLOC_W, AY_REALLOC_W, pol in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as HSlen. rewrite <- HSeq in HSlen.
  assert (H8 : H mod 8 = 0) by lia.
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  zstepA. shadow_fast HS (H + 40) 8.                  (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  apply evtA_done. eexists _. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ayf3_seg : forall (P : acc -> Prop) (ra gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (H SQ cb cx L bc D SBK SZ U : Z) (pew pad : word) (shbH : list byte),
  mem_inv asegs m1 -> 0 <= SQ < 2^47 ->
  rw_cells asegs m1 H (ahcells cb cx L pew bc pad D SBK SZ U H) ->
  u8arr asegs m1 (2147450880 + H / 8) shbH -> shbH = blk_shadow 104 ->
  0 < H -> H mod 16 = 0 -> H + 104 <= alloc_ceiling -> 17594333495296 <= H -> 0 <= L < 2^64 ->
  pol P H (H + 104) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) ->
  evtA asegs P (fun ms' => exists (a1' : word),
      ms' = MS (mkR (Z_to_bv 64 AYF_RET3) (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 H) (Z_to_bv 64 2147450880) (Z_to_bv 64 L) a1' a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_LEX_FREE) fc None m1 (seg_rom asegs))
    (MS (mkR ra (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 H) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AYF_RET2) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until shbH. intros MI SQR HC HS HSeq H0 H16 HHI HSH LR PH PHS.
  unfold ahcells in *. unfold AYF_RET2, AYF_RET3, AY_LEX_FREE, AY_FREE_W, AY_MALLOC_W, AY_REALLOC_W, pol in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as HSlen. rewrite <- HSeq in HSlen.
  assert (H8 : H mod 8 = 0) by lia.
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  zstepA. shadow_fast HS (H + 16) 8.                  (* [comment removed for export] *)
  zstepA.                                             (* [comment removed for export] *)
  stepA.                                              (* [comment removed for export] *)
  apply evtA_done. eexists _. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ayf4_seg : forall (P : acc -> Prop) (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 rav s0o s1o : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (H SQ lo cb cx L bc D SBK SZ U : Z) (pew pad : word) (junk shbH : list byte),
  stk asegs m1 lo SQ -> mem_inv asegs m1 -> alloc_ceiling <= lo -> lo <= SQ -> SQ + 32 <= 2^47 ->
  rw_cells asegs m1 H (ahcells cb cx L pew bc pad D SBK SZ U H) ->
  u8arr asegs m1 (2147450880 + H / 8) shbH -> shbH = blk_shadow 104 ->
  rw_cells asegs m1 SQ [CB 8 junk; C8 s1o; C8 s0o; C8 rav] ->
  0 < H -> H mod 16 = 0 -> H + 104 <= alloc_ceiling -> 17594333495296 <= H ->
  pol P lo (SQ + 32) -> pol P H (H + 104) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) ->
  evtA asegs P (fun ms' =>
      ms' = MS (mkR rav (Z_to_bv 64 (SQ + 32)) gp tp t0 (Z_to_bv 64 AY_FREE_W) t2 s0o s1o (Z_to_bv 64 0) (Z_to_bv 64 H) a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_FREE_W) fc None m1 (seg_rom asegs)
      /\ stk asegs m1 lo (SQ + 32))
    (MS (mkR (Z_to_bv 64 AYF_RET3) (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 H) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AYF_RET3) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until shbH. intros ST MI CEIL' LOQ SQH HC HS HSeq FR H0 H16 HHI HSH PSTK PH PHS.
  unfold ahcells in *. unfold AYF_RET3, AY_FREE_W, AY_MALLOC_W, AY_REALLOC_W, pol in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as HSlen. rewrite <- HSeq in HSlen.
  assert (H8 : H mod 8 = 0) by lia.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof (munch_refl ([] : list (Z * Z)) m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  zstepA. shadow_fast HS (H + 88) 8.                  (* [comment removed for export] *)
  zstepA. shadow_fast HS (H + 96) 8.                  (* [comment removed for export] *)
  zstepA. zstepA. stepA.                              (* [comment removed for export] *)
  do 4 stepA.                                         (* [comment removed for export] *)
  release_frame FR ST (SQ + 32).
  stepA.                                              (* [comment removed for export] *)
  apply evtA_done. split; [reflexivity | assumption].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section W.
Variable Y : ay_params.
Hypothesis KIPY : AHK_y_kip_stmt Y.
Hypothesis FRAMEY : AHK_y_frame_stmt Y.
Hypothesis BLKY : AHK_y_blocks_stmt Y.
Hypothesis BSHY : AHK_y_block_shadow_stmt Y.
Hypothesis BSMALL : AHK_y_small_high_stmt Y.   (* [comment removed for export] *)
Hypothesis LAYY : AHK_y_layout_stmt Y.
Hypothesis PERMY : AHK_y_perm_stmt Y.
Hypothesis RRT : ayR_trans_stmt Y.
Hypothesis RREFL : ayR_refl_stmt Y.
Hypothesis NONNEG : yacct_nonneg_stmt Y.
Hypothesis YFREE : yacct_free_stmt Y.
Hypothesis YPHI_HF : yphi_hand_free_stmt Y.
Hypothesis WFREE : aywrap_free_stmt Y.
Hypothesis BFREE : aybuf_free_stmt Y.
Hypothesis LFREE : aylex_free_stmt Y.
Variable URA : list Z.
Hypothesis UTRIV : forall m SP ra s0, bv_unsigned s0 < alloc_ceiling -> In (bv_unsigned ra) URA -> y_uanchor Y m SP ra s0.
Hypothesis URA_f1 : In 0x82b08 URA.                                            (* [comment removed for export] *)
Hypothesis URA_f2 : In 0x82b24 URA.                                            (* [comment removed for export] *)
Hypothesis URA_f3 : In 0x82b40 URA.                                            (* [comment removed for export] *)
Hypothesis UFRAME : forall m m' SP ra s0, (forall a, SP <= a < 2^47 -> m' (wa a) = m (wa a)) -> y_uanchor Y m SP ra s0 -> y_uanchor Y m' SP ra s0.

Ltac ay_statics_open STA :=
  let G1 := fresh "G1" in let G2 := fresh "G2" in let G3 := fresh "G3" in let G4 := fresh "G4" in
  destruct STA as (G1 & G2 & G3 & G4);
  unfold AY_GOT_SHADOW, AY_SHADOW_VAR, AY_GOT_UAR, AY_UAR_VAR, A_SB, wz in G1, G2, G3, G4.

(* [comment removed for export] *)
Lemma hand_cells_ahcells : forall m h mh pew pad,
  rw_cells asegs m (mh_addr mh) (hand_cells ayc h mh pew pad) <->
  rw_cells asegs m (mh_addr mh) (ahcells (yc_callbacks ayc) (mh_ctx mh) (mh_lexer mh) pew (h_bytesConsumed h) pad (mb_addr (mh_decbuf mh)) (mh_stack mh) (h_stack_size h) (h_used h) (mh_addr mh)).
Proof. aceil.
  intros. unfold hand_cells, hand_head_cells, alloc_cells, ahcells. cbn [app yc_malloc_w yc_realloc_w yc_free_w ayc]. unfold wz. tauto.
Qed.

Lemma perm_buf_front : forall (A : Type) (HD : A) (LX BB REST : list A),
  Permutation ((HD :: LX ++ BB) ++ REST) (BB ++ (HD :: LX) ++ REST).
Proof. aceil.
  intros. change ((HD :: LX ++ BB) ++ REST) with (((HD :: LX) ++ BB) ++ REST). rewrite <- app_assoc. apply Permutation_app_swap_app.
Qed.
Lemma perm_lex_front : forall (A : Type) (HD : A) (LX REST : list A),
  Permutation ((HD :: LX) ++ REST) (LX ++ HD :: REST).
Proof. aceil. intros. cbn. apply Permutation_middle. Qed.
Lemma perm_stack_front : forall (A : Type) (HD bs : A) (LX BB REST : list A),
  Permutation ((HD :: LX ++ BB ++ [bs]) ++ REST) (bs :: (HD :: LX ++ BB) ++ REST).
Proof. aceil.
  intros. symmetry. change (bs :: (HD :: LX ++ BB) ++ REST) with (bs :: ((HD :: LX ++ BB) ++ REST)).
  replace ((HD :: LX ++ BB ++ [bs]) ++ REST) with ((HD :: LX ++ BB) ++ bs :: REST); [apply Permutation_middle|].
  cbn. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma nbig_app : forall l1 l2, nbig (l1 ++ l2) = nbig l1 + nbig l2.
Proof. aceil. intros. unfold nbig. rewrite filter_app, length_app. lia. Qed.
Lemma nbig_le_len : forall l, nbig l <= Z.of_nat (length l).
Proof. aceil. intros l. unfold nbig. induction l as [|b l IH]; cbn; [lia|]. destruct (64512 <? ab_size b); cbn; lia. Qed.
(* [comment removed for export] *)
Lemma nbig_own : forall mh h,
  nbig (mkABlock (mh_addr mh) 104 :: abl (lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h)) ++ abl (buf_blocks (mh_decbuf mh) (h_decbuf h))) <= 2.
Proof. aceil.
  intros mh h. unfold lexer_blocks, buf_blocks.
  unfold nbig, abl, SIZEOF_LEXER, SIZEOF_BUF.
  destruct (yb_data (lx_buf (h_lexer h))); destruct (yb_data (h_decbuf h)); cbn -[Z.of_nat Z.le];
    repeat (match goal with |- context [64512 <? ?x] => destruct (64512 <? x) end); cbn -[Z.le]; lia.
Qed.

Lemma nbig_own1 : forall mh h,
  nbig (mkABlock (mh_addr mh) 104 :: abl (lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h))) <= 1.
Proof. aceil.
  intros mh h. unfold lexer_blocks, buf_blocks. unfold nbig, abl, SIZEOF_LEXER, SIZEOF_BUF.
  destruct (yb_data (lx_buf (h_lexer h))); cbn -[Z.of_nat Z.le];
    repeat (match goal with |- context [64512 <? ?x] => destruct (64512 <? x) end); cbn -[Z.le]; lia.
Qed.

Section Fn.
Variables (LF : list fblock) (REST : list ablock) (h : yhandle) (mh : mhand) (lo RR : Z) (K : TSet).
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (s : y_APS Y).
Hypothesis CONT : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (mo' : Model) (s' : y_APS Y),
  ayfree_rpost Y sp m mo s LF REST h mh lo RR a0' fc' m' mo' s' ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F' (ret_pc ra) fc' None m' (seg_rom asegs)) mo') K.
Hypothesis K0 : K [].
Hypothesis TP : tp = Z_to_bv 64 (c_tp ACONSTS).
Hypothesis CEIL : alloc_ceiling <= lo.
Hypothesis LO : lo <= bv_unsigned sp - (32 + (32 + (32 + 8192))).
Hypothesis SPH : bv_unsigned sp < 2^47.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis NBIG : nbig REST <= AY_NBIG_REST + 2.
Hypothesis HB1 : 0 <= h_bytesConsumed h < 2^31.
Hypothesis HB2 : 0 <= h_stack_size h < 2^31.
Hypothesis HB3 : 0 <= h_used h <= h_stack_size h.
Hypothesis HSH2 : 17594333495296 <= mh_addr mh.

Let HB : ablock := mkABlock (mh_addr mh) 104.
Let LXB : list ablock := abl (lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h)).
Let DBB : list ablock := abl (buf_blocks (mh_decbuf mh) (h_decbuf h)).

(* [comment removed for export] *)
Lemma ayfree_tail : forall (rav t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F1 : bvmap 5 word) (fc1 : bv 32)
    (m1 : mem) (mo1 : Model) (s1' : y_APS Y) (pew pad : word) (junk : list byte),
  y_AHK Y s1' ((HB :: LXB ++ DBB) ++ REST) LF m1 mo1 -> aystatics m1 ->
  rw_cells asegs m1 (bv_unsigned sp + -32) [CB 8 junk; C8 s1; C8 s0; C8 ra] -> stk asegs m1 lo (bv_unsigned sp + -32) -> mem_inv asegs m1 -> frm0 fc1 ->
  rw_cells asegs m1 (mh_addr mh) (ahcells (yc_callbacks ayc) (mh_ctx mh) (mh_lexer mh) pew (h_bytesConsumed h) pad (mb_addr (mh_decbuf mh)) (mh_stack mh) (h_stack_size h) (h_used h) (mh_addr mh)) ->
  alexer_rep m1 (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72) ->
  abuf_rep m1 (mh_decbuf mh) (h_decbuf h) (mh_addr mh + 72) ->
  oshadow m1 (mh_addr mh) 104 -> oshadow m1 (mh_lexer mh) 48 -> oshadow m1 (mb_addr (mh_lexbuf mh)) 32 -> oshadow m1 (mb_addr (mh_decbuf mh)) 32 ->
  ay_pres REST LF (bv_unsigned sp) [] m m1 -> (forall a, bv_unsigned sp <= a < 2^47 -> m1 (wa a) = m (wa a)) ->
  y_ayR Y s mo s1' mo1 -> y_SO Y s1' = y_SO Y s -> y_uanchor Y m (bv_unsigned sp) ra s0 ->
  y_phi_buf Y (h_decbuf h) + (y_free_cost Y + y_phi_buf Y (lx_buf (h_lexer h))) + y_free_cost Y + RR <= y_acredit Y s1' -> 0 <= RR ->
  realizes_cfg acfg asegs (mkCfg (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp t0 t1 t2 (Z_to_bv 64 (mh_addr mh)) (Z_to_bv 64 2147450880) a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F1 (Z_to_bv 64 AYF_RET1) fc1 None m1 (seg_rom asegs)) mo1) K.
Proof. aceil.
  intros until junk. intros AHK1 YS1 FR1 ST1 MI1 FRM1 HC LR BR OSH OSL OSLB OSDB PRES1 AGREE1 R1 SO1 UA CRED1 RR0.
  pose proof YFREE as YF0. unfold yacct_free_stmt in YF0.
  pose proof NONNEG as NN. destruct NN as (NN1 & NN2 & NN3 & NN4).
  pose proof (NN2 (lx_buf (h_lexer h))) as NNL. pose proof (NN2 (h_decbuf h)) as NND.
  destruct (BLKY _ _ _ _ _ AHK1) as (RNG & SEP & ND).
  assert (OWNR : forall b, In b (HB :: LXB ++ DBB) -> 0 < ab_addr b /\ ab_addr b mod 16 = 0 /\ ab_addr b + ab_size b <= alloc_ceiling /\ 0 <= ab_size b).
  { intros b Hb. pose proof (RNG b ltac:(apply in_or_app; left; exact Hb)) as X. unfold ablock_range, ACONSTS in X; aceil. cbn [c_img_hi] in X. lia. }
  pose proof (OWNR HB (or_introl eq_refl)) as RH. unfold HB in RH. cbn [ab_addr ab_size] in RH.
  assert (INL : In (mkABlock (mh_lexer mh) 48) (HB :: LXB ++ DBB)) by (right; apply in_or_app; left; left; reflexivity).
  assert (INLB : In (mkABlock (mb_addr (mh_lexbuf mh)) 32) (HB :: LXB ++ DBB)) by (right; apply in_or_app; left; right; left; reflexivity).
  assert (INDB : In (mkABlock (mb_addr (mh_decbuf mh)) 32) (HB :: LXB ++ DBB)) by (right; apply in_or_app; right; left; reflexivity).
  pose proof (OWNR _ INL) as RL. pose proof (OWNR _ INLB) as RLB. pose proof (OWNR _ INDB) as RDB. cbn [ab_addr ab_size] in RL, RLB, RDB.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -32)) = bv_unsigned sp + -32) by (apply unsigned_lit; lia).
  assert (DR : 0 <= mb_addr (mh_decbuf mh) < 2^64) by lia.
  assert (LRG : 0 <= mh_lexer mh < 2^64) by lia.
  pose proof OSH as OSH0. destruct OSH as (H8 & _ & HSu). unfold A_SB in HSu.
  (* [comment removed for export] *)
  unfold AYF_RET1. arz_seg KIPY AHK1. ret_pc_lit.
  pose proof (aypol_opol_block Y _ LF _ _ LINK HB ltac:(left; reflexivity) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia)
                ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PH PHS].
  unfold HB in PH, PHS. cbn [ab_addr ab_size] in PH, PHS. unfold oshw_lo, oshw_hi, A_SB, amem in PH, PHS. cbn in PHS.
  eapply evtA_cut.
  { eapply (ayf2_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mh_addr mh) (bv_unsigned sp + -32));
      [ exact MI1 | lia | exact HC | exact HSu | reflexivity | lia | lia | lia | lia | exact DR | exact PH | intros a k Ha Hk; apply PHS; lia ]. }
  cbv beta. intros ms2 (a1x & ->).
  apply evtA_done. intros mo2 Hag2 HLI2 Hh2.
  destruct (BACK mo2 Hag2 HLI2) as [AHK2 R2]. clear LINK BACK PH PHS.
  assert (AHK2' : y_AHK Y s1' (DBB ++ (HB :: LXB) ++ REST) LF m1 mo2) by (eapply PERMY; [exact AHK2| apply perm_buf_front| apply Permutation_refl]).
  pose proof HC as HC2. apply (proj2 (hand_cells_ahcells _ _ _ _ _)) in HC2. apply hand_cells_app in HC2. destruct HC2 as [HH HA].
  (* [comment removed for export] *)
  eapply (BFREE LF ((HB :: LXB) ++ REST) (mh_decbuf mh) (h_decbuf h) (mh_addr mh + 72) lo ((y_free_cost Y + y_phi_buf Y (lx_buf (h_lexer h))) + y_free_cost Y + RR));
    [ exact K0
    | apply AYST_split; split; [exact AHK2'| exact YS1]
    | exact BR
    | exact HA
    | exists HB; split; [left; reflexivity|]; unfold HB; cbn [ab_addr ab_size]; split; [lia|]; split; [lia|]; split; [clear -CEILB RH; Z.div_mod_to_equations; lia|]; split; [exact OSH0| unfold oshw_hi, A_SB; cbn; clear -CEILB HSH2; lia]
    | exact OSDB
    | unfold ayframe_pre, AY_BUF_FREE_STACK, AMALLOC_STACK; aceil; rewrite ESP;
      split; [exact ST1|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [clear -CEILB SP16 SR; Z.div_mod_to_equations; lia|];
      split; [exact MI1|]; split; [exact TP| exact FRM1]
    | reflexivity
    | lia
    | lia
    | unfold HB, LXB; rewrite nbig_app; pose proof (nbig_own1 mh h) as NBO; unfold AY_NBIG_REST in *; lia
    | apply UTRIV; [rewrite unsigned_lit by lia; aceil; lia| unfold AYF_RET2; rewrite unsigned_lit by lia; exact URA_f2]
    | ].
  cbv beta. intros t0' t1' t2' a0' a1'' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 mo3 sa2 (SO2 & R3 & CRED2 & (MI2 & ST2 & FRM2 & _ & PRES2) & HA2 & AY2).
  rewrite ESP in ST2, PRES2. unfold AYF_RET2.
  apply AYST_split in AY2. destruct AY2 as [AHK3 YS3].
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR1 ltac:(lia)) as FR3. clear FR1.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES2 HC ltac:(exists HB; split; [left; reflexivity| unfold HB; cbn; rewrite ?hand_cells_size; lia])) as HC3. clear HC HH HA.
  assert (LR3 : alexer_rep m2 (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72)).
  { eapply lexer_rep_agree; [eapply ay_pres_agree; exact PRES2| exact LR| | |].
    - intros a Ha. split; [right; left; exists (mkABlock (mh_lexer mh) 48); split; [right; left; reflexivity| cbn; unfold SIZEOF_LEXER in Ha; lia]| intros F0; exact F0].
    - intros a Ha. split; [right; left; exists (mkABlock (mb_addr (mh_lexbuf mh)) 32); split; [right; right; left; reflexivity| cbn; unfold SIZEOF_BUF in Ha; lia]| intros F0; exact F0].
    - intros HD a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_data (mh_lexbuf mh)) (yb_len (lx_buf (h_lexer h)))).
      split; [| cbn; lia]. unfold LXB, lexer_blocks, buf_blocks. destruct (yb_data (lx_buf (h_lexer h))); [| exfalso; apply HD; reflexivity].
      cbn. right; right; right; left; reflexivity. }
  clear LR.
  assert (PRES3 : ay_pres REST LF (bv_unsigned sp) [] m m2).
  { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0| auto| auto]. }
  assert (AGREE3 : forall a, bv_unsigned sp <= a < 2^47 -> m2 (wa a) = m (wa a)).
  { intros a Ha. rewrite <- (AGREE1 a Ha). destruct (PRES2 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  destruct (BLKY _ _ _ _ _ AHK3) as (RNG3 & SEP3 & ND3).
  pose proof (BSHY _ _ _ _ _ HB AHK3 (or_introl eq_refl) ltac:(unfold HB; cbn; lia)) as [OSH3 _]. unfold HB in OSH3. cbn [ab_addr ab_size] in OSH3.
  pose proof (BSHY _ _ _ _ _ (mkABlock (mh_lexer mh) 48) AHK3 ltac:(right; left; reflexivity) ltac:(cbn; lia)) as [OSL3 _]. cbn [ab_addr ab_size] in OSL3.
  pose proof (BSHY _ _ _ _ _ (mkABlock (mb_addr (mh_lexbuf mh)) 32) AHK3 ltac:(right; right; left; reflexivity) ltac:(cbn; lia)) as [OSLB3 _]. cbn [ab_addr ab_size] in OSLB3.
  pose proof OSH3 as OSH3'. destruct OSH3' as (_ & _ & HSu3). unfold A_SB in HSu3.
  clear PRES2 MI1 ST1 AHK1 AHK2 AHK2' YS1 OSH0 OSL OSLB OSDB HSu BR.
  (* [comment removed for export] *)
  arz_seg KIPY AHK3. ret_pc_lit.
  pose proof (aypol_opol_block Y _ LF _ _ LINK HB ltac:(left; reflexivity) ltac:(unfold HB; cbn; lia) ltac:(unfold HB; cbn; unfold oshw_lo, A_SB; lia)
                ltac:(unfold HB; cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(unfold HB; cbn; lia)) as [PH PHS].
  unfold HB in PH, PHS. cbn [ab_addr ab_size] in PH, PHS. unfold oshw_lo, oshw_hi, A_SB, amem in PH, PHS. cbn in PHS.
  eapply evtA_cut.
  { eapply (ayf3_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mh_addr mh) (bv_unsigned sp + -32));
      [ exact MI2 | lia | exact HC3 | exact HSu3 | reflexivity | lia | lia | lia | lia | exact LRG | exact PH | intros a k Ha Hk; apply PHS; lia ]. }
  cbv beta. intros ms4 (a1y & ->).
  apply evtA_done. intros mo4 Hag4 HLI4 Hh4.
  destruct (BACK mo4 Hag4 HLI4) as [AHK4 R4]. clear LINK BACK PH PHS.
  assert (AHK4' : y_AHK Y sa2 (LXB ++ HB :: REST) LF m2 mo4) by (eapply PERMY; [exact AHK4| apply perm_lex_front| apply Permutation_refl]).
  pose proof HC3 as HC4. apply (proj2 (hand_cells_ahcells _ _ _ _ _)) in HC4. apply hand_cells_app in HC4. destruct HC4 as [HH4 HA4].
  (* [comment removed for export] *)
  eapply (LFREE LF (HB :: REST) (mh_lexer mh) (mh_addr mh + 72) (mh_lexbuf mh) (h_lexer h) lo (y_free_cost Y + RR));
    [ exact K0
    | apply AYST_split; split; [unfold LXB, lexer_blocks in AHK4'; rewrite abl_cons in AHK4'; exact AHK4'| exact YS3]
    | exact LR3
    | exact HA4
    | exists HB; split; [left; reflexivity|]; unfold HB; cbn [ab_addr ab_size]; split; [lia|]; split; [lia|]; split; [clear -CEILB RH; Z.div_mod_to_equations; lia|]; split; [exact OSH3| unfold oshw_hi, A_SB; cbn; clear -CEILB HSH2; lia]
    | exact OSL3
    | exact OSLB3
    | unfold ayframe_pre, AY_LEX_FREE_STACK, AY_BUF_FREE_STACK, AMALLOC_STACK; aceil; rewrite ESP;
      split; [exact ST2|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [clear -CEILB SP16 SR; Z.div_mod_to_equations; lia|];
      split; [exact MI2|]; split; [exact TP| exact FRM2]
    | reflexivity
    | lia
    | lia
    | change (nbig (HB :: REST)) with (nbig REST); unfold AY_NBIG_REST in *; lia
    | apply UTRIV; [rewrite unsigned_lit by lia; aceil; lia| unfold AYF_RET3; rewrite unsigned_lit by lia; exact URA_f3]
    | ].
  cbv beta. intros t0'' t1'' t2'' a0'' a1w a2'' a3'' a4'' a5'' a6'' a7'' t3'' t4'' t5'' t6'' F5 fc5 m5 mo5 sa5 (SO5 & R5 & CRED5 & (MI5 & ST5 & FRM5 & _ & PRES5) & HA5 & AY5).
  rewrite ESP in ST5, PRES5. unfold AYF_RET3.
  apply AYST_split in AY5. destruct AY5 as [AHK6 YS6].
  pose proof (aypres_frame _ _ _ _ _ _ _ PRES5 FR3 ltac:(lia)) as FR6. clear FR3.
  pose proof (aypres_block _ _ _ _ _ _ _ PRES5 HC3 ltac:(exists HB; split; [left; reflexivity| unfold HB; cbn; rewrite ?hand_cells_size; lia])) as HC6. clear HC3 HH4 HA4.
  assert (PRES6 : ay_pres REST LF (bv_unsigned sp) [] m m5).
  { eapply ay_pres_trans; [exact PRES3|]. eapply (ay_pres_weaken Y); [exact PRES5| lia| intros b0 Hb0; right; exact Hb0| auto| auto]. }
  assert (AGREE6 : forall a, bv_unsigned sp <= a < 2^47 -> m5 (wa a) = m (wa a)).
  { intros a Ha. rewrite <- (AGREE3 a Ha). destruct (PRES5 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
  pose proof (BSHY _ _ _ _ _ HB AHK6 (or_introl eq_refl) ltac:(unfold HB; cbn; lia)) as [OSH6 _]. unfold HB in OSH6. cbn [ab_addr ab_size] in OSH6.
  pose proof OSH6 as OSH6'. destruct OSH6' as (_ & _ & HSu6). unfold A_SB in HSu6.
  clear PRES5 MI2 ST2 AHK3 AHK4 AHK4' YS3 OSH3 OSL3 OSLB3 HSu3 LR3.
  (* [comment removed for export] *)
  arz_seg KIPY AHK6. ret_pc_lit.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_opol_block Y _ LF _ _ LINK HB ltac:(left; reflexivity) ltac:(unfold HB; cbn; lia) ltac:(unfold HB; cbn; unfold oshw_lo, A_SB; lia)
                ltac:(unfold HB; cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(unfold HB; cbn; lia)) as [PH PHS].
  unfold HB in PH, PHS. cbn [ab_addr ab_size] in PH, PHS. unfold oshw_lo, oshw_hi, A_SB, amem in PH, PHS. cbn in PHS.
  eapply evtA_cut.
  { eapply (ayf4_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mh_addr mh) (bv_unsigned sp + -32) lo);
      [ exact ST5 | exact MI5 | lia | lia | lia | exact HC6 | exact HSu6 | reflexivity | exact FR6 | lia | lia | lia | lia
      | intros a k Ha Hk; apply PSTK; lia | exact PH | intros a k Ha Hk; apply PHS; lia ]. }
  cbv beta. intros ms7 (-> & ST7).
  apply evtA_done. intros mo7 Hag7 HLI7 Hh7.
  destruct (BACK mo7 Hag7 HLI7) as [AHK7 R7]. clear LINK BACK PSTK PH PHS.
  replace (bv_unsigned sp + -32 + 32) with (bv_unsigned sp) in * by lia. rewrite Z_to_bv_bv_unsigned.
  (* [comment removed for export] *)
  eapply (WFREE (mh_addr mh) 104 _ LF lo RR);
    [ exact K0
    | apply AYST_split; split; [exact AHK7| exact YS6]
    | left; reflexivity
    | reflexivity
    | lia
    | exact RR0
    | change (nbig (HB :: REST)) with (nbig REST); unfold AY_NBIG_REST in *; lia
    | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil;
      split; [exact ST7|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [exact SP16|]; split; [exact MI5|]; split; [exact TP| exact FRM5]
    | eapply UFRAME; [exact AGREE6| exact UA]
    | ].
  cbv beta. intros t0x t1x t2x a0x a1z a2x a3x a4x a5x a6x a7x t3x t4x t5x t6x F8 fc8 m8 mo8 sa8 (MI8 & ST8 & FRM8 & _ & PRES8) SO8 R8 CRED8 AY8.
  unfold HB in PRES8, AY8. rewrite ab_remove_head in PRES8, AY8.
  eapply CONT. unfold ayfree_rpost.
  split; [rewrite SO8, SO5, SO2; exact SO1|].
  split; [eapply RRT; [exact R1|]; eapply RRT; [exact R2|]; eapply RRT; [exact R3|]; eapply RRT; [exact R4|]; eapply RRT; [exact R5|]; eapply RRT; [exact R7| exact R8]|].
  split; [lia|].
  split.
  { split; [exact MI8|]. split; [exact ST8|]. split; [exact FRM8|]. split; [exact I|]. eapply ay_pres_trans; [exact PRES6| exact PRES8]. }
  exact AY8.
Qed.
End Fn.

Theorem ayfree_proof : ayfree_stmt Y.
Proof. aceil.
  unfold ayfree_stmt. intros LF REST h mh lo RR K. intros until s. intros K0 AY HR OSH OSL OSLB OSDB FP EA CRED RR0 NBIG UA CONT. subst a0.
  destruct FP as (ST & CEIL & LO & SPH & SP16 & MI & TP & FRM).
  apply AYST_split in AY. destruct AY as [AHK0 YS]. pose proof YS as (_ & _ & _ & STA). ay_statics_open STA.
  destruct (BLKY _ _ _ _ _ AHK0) as (RNG & SEP & ND).
  pose proof HR as HR0. destruct HR as (HS & LR & BR & BSR). destruct HS as ((pew & pad & HC & PEW) & HB1 & HB2 & HB3 & HB4).
  apply hand_cells_ahcells in HC.
  pose proof (yb_in_hand mh h) as INH. pose proof (yb_in_lexer mh h) as INL. pose proof (yb_in_lexbuf mh h) as INLB. pose proof (yb_in_decbuf mh h) as INDB.
  assert (OWNR : forall b, In b (abl (yblocks mh h)) -> 0 < ab_addr b /\ ab_addr b mod 16 = 0 /\ ab_addr b + ab_size b <= alloc_ceiling /\ 0 <= ab_size b).
  { intros b Hb. pose proof (RNG b ltac:(apply in_or_app; left; exact Hb)) as X. unfold ablock_range, ACONSTS in X. cbn [c_img_hi] in X. lia. }
  pose proof (OWNR _ INH) as RH. cbn [ab_addr ab_size] in RH.
  pose proof (BSMALL _ _ _ _ _ _ AHK0 ltac:(apply in_or_app; left; exact INH) ltac:(cbn; unfold SIZEOF_BUF, SIZEOF_LEXER, SIZEOF_HANDLE; lia)) as HSHI. cbn [ab_addr] in HSHI.
  unfold oshw_hi, A_SB, amem in HSHI. assert (HSH2 : 17594333495296 <= mh_addr mh) by (revert HSHI CEILB; clear; intros HH CEILB; cbn in HH; lia). clear HSHI.
  unfold AY_FREE_STACK, AY_LEX_FREE_STACK, AY_BUF_FREE_STACK, AMALLOC_STACK, SIZEOF_HANDLE, SIZEOF_LEXER, SIZEOF_BUF, wz in *.
  aceil.
  pose proof OSH as OSH0. destruct OSH as (H8 & _ & HSu). unfold A_SB in HSu.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  assert (SBR : 0 <= mh_stack mh < 2^64).
  { destruct (h_stack_blk h) as [sb|] eqn:ESB.
    - pose proof (OWNR _ (yb_in_stack mh h ltac:(rewrite ESB; discriminate))) as X. cbn [ab_addr ab_size] in X. lia.
    - rewrite (proj1 HB4 eq_refl). lia. }
  (* [comment removed for export] *)
  arz_seg KIPY AHK0.
  pose proof (aypol_stack Y _ LF _ _ LINK lo (bv_unsigned sp) ltac:(aceil; lia) ltac:(lia)) as PSTK.
  pose proof (aypol_img Y _ LF _ _ LINK) as PIMG. unfold AY_IMG_LO, AY_IMG_HI in PIMG.
  pose proof (aypol_opol_block Y _ LF _ _ LINK (mkABlock (mh_addr mh) 104) ltac:(apply in_or_app; left; exact INH) ltac:(cbn; lia) ltac:(cbn; unfold oshw_lo, A_SB; lia) ltac:(cbn; unfold oshw_hi, A_SB, amem; lia) ltac:(cbn; lia)) as [PH PHS].
  cbn [ab_addr ab_size] in PH, PHS. unfold oshw_lo, oshw_hi, A_SB, amem in PH, PHS.
  eapply evtA_cut.
  { eapply (ayf1_seg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (mh_addr mh) lo);
      [ exact ST | exact MI | lia | lia | lia | exact HC | exact HSu | reflexivity | exact G1 | exact G2
      | lia | lia | lia | lia | exact SBR | exact PSTK | exact PIMG | exact PH | intros a k Ha Hk; apply PHS; lia ]. }
  cbv beta. intros ms1 (a0' & a1' & a2' & junk & m1 & MU & WM & MI1 & ST1 & FR1 & CASES).
  (* [comment removed for export] *)
  assert (POST1 : forall mo1, magree mo mo1 -> LI (y_aS Y s) (y_aN Y s) (y_aEB Y s) mo1 ->
            y_AHK Y s (abl (yblocks mh h) ++ REST) LF m1 mo1 /\ y_ayR Y s mo s mo1).
  { intros mo1 Hag1 HLI1. destruct (BACK mo1 Hag1 HLI1) as [AHKb R1]. split; [| exact R1].
    eapply FRAMEY; [exact AHKb| exact MU| exact WM|]. constructor; [left; cbn [fst snd]; aceil; lia| constructor]. }
  pose proof (aystatics_munch _ _ _ YS MU WM ltac:(constructor; [cbn [fst snd]; lia| constructor])) as YS1.
  assert (HR1 : ahand_rep m1 h mh).
  { eapply hand_rep_below; [exact HR0| exact MU| exact WM| constructor; [cbn [fst]; apply Z.le_refl| constructor]|].
    intros b Hb. pose proof (OWNR b Hb). lia. }
  eapply (rw_cells_transport asegs) in HC; [| exact MU| exact WM| cbv [disjoint_from fst snd]; cbn [cells_size csize Nat.add length ahcells]; rewrite ?hand_cells_size; lia].
  assert (PRES1 : ay_pres REST LF (bv_unsigned sp) [] m m1).
  { eapply ay_pres_of_munch; [exact MU| exact WM|]. intros a Ha Hc _.
    eapply (ay_client_outside_stack Y BLKY LAYY _ _ _ _ _ REST (bv_unsigned sp)); [exact AHK0| intros b0 Hb0; apply in_or_app; right; exact Hb0| aceil; lia| lia| exact Hc]. }
  assert (AGREE1 : forall a, bv_unsigned sp <= a < 2^47 -> m1 (wa a) = m (wa a)) by (intros a Ha; apply MU; rewrite wa_unsigned by lia; cbn; lia).
  assert (OSH1 : oshadow m1 (mh_addr mh) 104) by (eapply oshadow_below; [exact OSH0| exact MU| exact WM| constructor; [cbn [fst]; apply Z.le_refl| constructor]| lia| lia| lia]).
  assert (OSL1 : oshadow m1 (mh_lexer mh) 48).
  { pose proof (OWNR _ INL) as X. cbn [ab_addr ab_size] in X. eapply oshadow_below; [exact OSL| exact MU| exact WM| constructor; [cbn [fst]; apply Z.le_refl| constructor]| lia| lia| lia]. }
  assert (OSLB1 : oshadow m1 (mb_addr (mh_lexbuf mh)) 32).
  { pose proof (OWNR _ INLB) as X. cbn [ab_addr ab_size] in X. eapply oshadow_below; [exact OSLB| exact MU| exact WM| constructor; [cbn [fst]; apply Z.le_refl| constructor]| lia| lia| lia]. }
  assert (OSDB1 : oshadow m1 (mb_addr (mh_decbuf mh)) 32).
  { pose proof (OWNR _ INDB) as X. cbn [ab_addr ab_size] in X. eapply oshadow_below; [exact OSDB| exact MU| exact WM| constructor; [cbn [fst]; apply Z.le_refl| constructor]| lia| lia| lia]. }
  clear LINK BACK PSTK PIMG PH PHS HSu ST MI.
  pose proof YFREE as YF0. unfold yacct_free_stmt in YF0.
  pose proof NONNEG as NN. destruct NN as (NN1 & NN2 & NN3 & NN4).
  pose proof (NN2 (lx_buf (h_lexer h))) as NNL. pose proof (NN2 (h_decbuf h)) as NND.
  pose proof (YPHI_HF h 0) as PHF.
  destruct HR1 as (HS1 & LR1 & BR1 & BSR1).
  pose proof (TAIL := ayfree_tail LF REST h mh lo RR K ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m mo s CONT K0 TP CEIL LO SPH SP16 NBIG HSH2).
  destruct CASES as [[SB0 ->] | [SBNZ ->]].
  - (* [comment removed for export] *)
    assert (ESB : h_stack_blk h = None) by (apply (proj2 HB4); exact SB0).
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (POST1 mo1 Hag1 HLI1) as [AHK1 R1].
    unfold yblocks, bs_blocks in AHK1. rewrite ESB, app_nil_r in AHK1. rewrite abl_cons, abl_app in AHK1.
    eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 mo1 s pew pad junk);
      [ exact AHK1 | exact YS1 | exact FR1 | exact ST1 | exact MI1 | exact FRM | exact HC | exact LR1 | exact BR1
      | exact OSH1 | exact OSL1 | exact OSLB1 | exact OSDB1 | exact PRES1 | exact AGREE1 | exact R1 | reflexivity | exact UA | lia | exact RR0 ].
  - (* [comment removed for export] *)
    assert (ESB : h_stack_blk h <> None) by (intros E; apply SBNZ; apply (proj1 HB4); exact E).
    destruct (h_stack_blk h) as [sbk|] eqn:ESB'; [| exfalso; exact (ESB eq_refl)].
    apply evtA_done. intros mo1 Hag1 HLI1 Hh1. destruct (POST1 mo1 Hag1 HLI1) as [AHK1 R1].
    unfold yblocks, bs_blocks in AHK1. rewrite ESB' in AHK1. rewrite abl_cons, !abl_app in AHK1. cbn [abl map] in AHK1.
    lazymatch type of AHK1 with y_AHK Y s ((?HBx :: ?LXBx ++ ?DBBx ++ [?SBx]) ++ REST) LF m1 mo1 =>
      assert (AHK1' : y_AHK Y s (SBx :: (HBx :: LXBx ++ DBBx) ++ REST) LF m1 mo1) by (eapply PERMY; [exact AHK1| apply perm_stack_front| apply Permutation_refl]) end.
    destruct (BLKY _ _ _ _ _ AHK1') as (_ & _ & ND1).
    name_sp sp (-32)%Z. rewrite <- Hsp in ST1.
    eapply (WFREE (mh_stack mh) (h_stack_size h) _ LF lo (y_phi_buf Y (h_decbuf h) + (y_free_cost Y + y_phi_buf Y (lx_buf (h_lexer h))) + y_free_cost Y + RR));
      [ exact K0
      | apply AYST_split; split; [exact AHK1'| exact YS1]
      | left; reflexivity
      | reflexivity
      | lia
      | lia
      | lazymatch goal with |- nbig (?sb :: ?own ++ REST) <= _ =>
          pose proof (nbig_cons_le sb (own ++ REST)) as NB1; rewrite nbig_app in NB1; pose proof (nbig_own mh h) as NB2;
          unfold AY_NBIG_REST, SIZEOF_HANDLE in *; lia end
      | unfold ayframe_pre, AY_WRAP_STACK, AMALLOC_STACK; aceil;
        split; [exact ST1|]; split; [lia|]; split; [lia|]; split; [lia|]; split; [rewrite Hsp; clear -CEILB SP16 SR; Z.div_mod_to_equations; lia|]; split; [exact MI1|]; split; [exact TP| exact FRM]
      | apply UTRIV; [rewrite unsigned_lit by lia; aceil; lia| unfold AYF_RET1; rewrite unsigned_lit by lia; exact URA_f1]
      | ].
    cbv beta. intros t0' t1' t2' a0'' a1'' a2'' a3' a4' a5' a6' a7' t3' t4' t5' t6' F2 fc2 m2 mo2 sa2 (MI2 & ST2 & FRM2 & _ & PRES2) SO2 R2 CRED2 AY2.
    unname_sp. rewrite ab_remove_head in PRES2, AY2. unfold AYF_RET1.
    replace (ret_pc (Z_to_bv 64 535304)) with (Z_to_bv 64 535304) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply AYST_split in AY2. destruct AY2 as [AHK2 YS2].
    pose proof (aypres_frame _ _ _ _ _ _ _ PRES2 FR1 ltac:(lia)) as FR2.
    pose proof (aypres_block _ _ _ _ _ _ _ PRES2 HC ltac:(exists (mkABlock (mh_addr mh) 104); split; [left; reflexivity| cbn; rewrite ?hand_cells_size; lia])) as HC2.
    assert (AGP : agree_on asegs (fun a => ay_client_addr ((mkABlock (mh_addr mh) 104 :: abl (lexer_blocks (mh_lid mh) (mh_lexer mh) (mh_lexbuf mh) (h_lexer h)) ++ abl (buf_blocks (mh_decbuf mh) (h_decbuf h))) ++ REST) LF (bv_unsigned sp + -32) a /\ ~ yin_ivs [] a) m1 m2) by (apply ay_pres_agree; exact PRES2).
    assert (LR2 : alexer_rep m2 (mh_lexer mh) (h_lexer h) (mh_lexbuf mh) (mh_addr mh + 72)).
    { eapply lexer_rep_agree; [exact AGP| exact LR1| | |].
      - intros a Ha. split; [right; left; exists (mkABlock (mh_lexer mh) 48); split; [right; apply in_or_app; left; left; reflexivity| cbn; unfold SIZEOF_LEXER in Ha; lia]| intros F0; exact F0].
      - intros a Ha. split; [right; left; exists (mkABlock (mb_addr (mh_lexbuf mh)) 32); split; [right; apply in_or_app; left; right; left; reflexivity| cbn; unfold SIZEOF_BUF in Ha; lia]| intros F0; exact F0].
      - intros HD a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_data (mh_lexbuf mh)) (yb_len (lx_buf (h_lexer h)))).
        split; [| cbn; lia]. unfold lexer_blocks, buf_blocks. destruct (yb_data (lx_buf (h_lexer h))); [| exfalso; apply HD; reflexivity].
        cbn. right; right; right; left; reflexivity. }
    assert (BR2 : abuf_rep m2 (mh_decbuf mh) (h_decbuf h) (mh_addr mh + 72)).
    { eapply buf_rep_agree; [exact AGP| exact BR1| |].
      - intros a Ha. split; [right; left; exists (mkABlock (mb_addr (mh_decbuf mh)) 32); split; [right; apply in_or_app; left; apply in_or_app; right; left; reflexivity| cbn; unfold SIZEOF_BUF in Ha; lia]| intros F0; exact F0].
      - intros HD a Ha. split; [| intros F0; exact F0]. right; left. exists (mkABlock (mb_data (mh_decbuf mh)) (yb_len (h_decbuf h))).
        split; [| cbn; lia]. right. apply in_or_app. left. apply in_or_app. right.
        unfold buf_blocks. destruct (yb_data (h_decbuf h)); [| exfalso; apply HD; reflexivity]. cbn. right; left; reflexivity. }
    destruct (BLKY _ _ _ _ _ AHK2) as (RNG2 & _ & _).
    pose proof (BSHY _ _ _ _ _ (mkABlock (mh_addr mh) 104) AHK2 ltac:(left; reflexivity) ltac:(cbn; lia)) as [OSH2 _]. cbn [ab_addr ab_size] in OSH2.
    pose proof (BSHY _ _ _ _ _ (mkABlock (mh_lexer mh) 48) AHK2 ltac:(right; apply in_or_app; left; left; reflexivity) ltac:(cbn; lia)) as [OSL2 _]. cbn [ab_addr ab_size] in OSL2.
    pose proof (BSHY _ _ _ _ _ (mkABlock (mb_addr (mh_lexbuf mh)) 32) AHK2 ltac:(right; apply in_or_app; left; right; left; reflexivity) ltac:(cbn; lia)) as [OSLB2 _]. cbn [ab_addr ab_size] in OSLB2.
    pose proof (BSHY _ _ _ _ _ (mkABlock (mb_addr (mh_decbuf mh)) 32) AHK2 ltac:(right; apply in_or_app; left; apply in_or_app; right; left; reflexivity) ltac:(cbn; lia)) as [OSDB2 _]. cbn [ab_addr ab_size] in OSDB2.
    assert (PRES2w : ay_pres REST LF (bv_unsigned sp) [] m m2).
    { eapply ay_pres_trans; [exact PRES1|]. eapply (ay_pres_weaken Y); [exact PRES2| lia| intros b0 Hb0; apply in_or_app; right; exact Hb0| auto| auto]. }
    assert (AGREE2 : forall a, bv_unsigned sp <= a < 2^47 -> m2 (wa a) = m (wa a)).
    { intros a Ha. rewrite <- (AGREE1 a Ha). destruct (PRES2 a ltac:(lia) ltac:(left; lia) ltac:(intros F0; exact F0)) as [E _]. exact E. }
    rewrite abl_cons in AHK2.
    eapply (TAIL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 mo2 sa2 pew pad junk);
      [ exact AHK2 | exact YS2 | exact FR2 | exact ST2 | exact MI2 | exact FRM2 | exact HC2 | exact LR2 | exact BR2
      | exact OSH2 | exact OSL2 | exact OSLB2 | exact OSDB2 | exact PRES2w | exact AGREE2
      | eapply RRT; [exact R1| exact R2] | exact SO2 | exact UA | lia | exact RR0 ].
Qed.
End W.
End RC__2.
