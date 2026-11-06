(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AYajlRep AYajl_iface AY_hand.
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
Definition AAL_RET1 : Z := 0x824fc.   (* [comment removed for export] *)
Definition AAL_RET2 : Z := 0x8260c.   (* [comment removed for export] *)
Definition AAL_RET3 : Z := 0x82640.   (* [comment removed for export] *)

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma aal1_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (CBK CFGP AFS CX lo : Z),
  stk asegs m1 lo (bv_unsigned sp) -> mem_inv asegs m1 -> alloc_ceiling <= lo -> lo + 1024 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 ->
  rw_cells asegs m1 674224 [C8 (Z_to_bv 64 711544)] -> rw_cells asegs m1 711544 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells asegs m1 674312 [C8 (Z_to_bv 64 711552)] -> rw_cells asegs m1 711552 [C4 (Z_to_bv 64 1)] ->
  0 <= CBK < 2^64 -> 0 <= CFGP < 2^64 -> 0 <= AFS < 2^64 -> 0 <= CX < 2^64 ->
  pol P lo (bv_unsigned sp) -> pol P 0x10000 0x603000 ->
  evtA asegs P (fun ms' => exists (SQ : Z) (jq : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AAL_RET1) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 96) (Z_to_bv 64 711544) (sx32 (Z_to_bv 64 1)) (Z_to_bv 64 CX) a4 a5 a6 a7
                   s2 s3 (Z_to_bv 64 AFS) s5 s6 (Z_to_bv 64 CFGP) (Z_to_bv 64 CBK) (Z_to_bv 64 2147450880) (Z_to_bv 64 CX) s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_STACK_MALLOC_1) fc None m' (seg_rom asegs)
      /\ SQ mod 32 = 0 /\ bv_unsigned sp - 176 <= SQ <= bv_unsigned sp - 160
      /\ munch [(lo, bv_unsigned sp)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo SQ
      /\ rw_cells asegs m' SQ [CB 56 jq]
      /\ rw_cells asegs m' (bv_unsigned sp + -104) [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk asegs m' (SQ + 56) (bv_unsigned sp + -104))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 CBK) (Z_to_bv 64 CFGP) (Z_to_bv 64 AFS) (Z_to_bv 64 CX) a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_ALLOC) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until lo. intros ST MI CEIL LOQ SPH SP16 G1 G2 G3 G4 R1 R2 R3 R4 PSTK PIMG. unfold AY_ALLOC, AAL_RET1, AY_STACK_MALLOC_1, pol in *.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  carve_frame 160%nat ST.
  stepA. apply (rw_cells_split_CB asegs _ _ [] 160 _ [] [8;48;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  do 14 stepA.                                             (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  rewrite (unsigned_lit (bv_unsigned sp + -160)) by lia. rewrite (land_align32 (bv_unsigned sp + -160)) by lia.
  remember (bv_unsigned sp + -160 - (bv_unsigned sp + -160) mod 32) as SQ eqn:SQE.
  assert (SQF : SQ mod 32 = 0 /\ bv_unsigned sp - 176 <= SQ <= bv_unsigned sp - 160) by (subst SQ; clear -SP16; Z.div_mod_to_equations; lia).
  clear SQE.
  (* [comment removed for export] *)
  match type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
    apply (proj1 (ycells_app asegs _ _ [c0; c1] rest)) in FR end.
  destruct FR as [FRlo SV]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV.
  pose proof (stk_release asegs _ _ _ _ ST FRlo ltac:(lia)) as ST'. clear ST FRlo. cbn [cells_size csize Nat.add] in ST'.
  pose proof (proj2 (stk_split asegs _ _ (SQ + 56) _ ST' ltac:(lia))) as GAP.
  destruct (stk_carve_at _ _ _ SQ 56 ST' ltac:(lia) ltac:(cbn; lia)) as [ST [jq FR]]. clear ST'.
  replace (bv_unsigned sp + -160 + Z.of_nat 56) with (bv_unsigned sp + -104) in SV, GAP by lia.
  stepA.                                                   (* [comment removed for export] *)
  stepA. stepA. stepA.                                     (* [comment removed for export] *)
  do 4 stepA.                                              (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  zstepA. if_false.                                        (* [comment removed for export] *)
  stepA. stepA.                                            (* [comment removed for export] *)
  apply evtA_done. cbv beta. eexists SQ, _, _. split; [reflexivity|].
  split; [exact (proj1 SQF)|]. split; [exact (proj2 SQF)|].
  repeat match goal with |- _ /\ _ => split end; try assumption; try exact FR; exact GAP.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFA_MAGIC : Z := 0x41b58ab3.
Definition AFA_DESCR : Z := 0x14879.

Lemma aal2_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ ff lo : Z) (jq fj : list byte) (ffp : word),
  stk asegs m1 lo SQ -> mem_inv asegs m1 -> alloc_ceiling <= lo -> lo + 1024 <= SQ -> SQ + 192 <= 2^47 ->
  SQ mod 32 = 0 ->
  rw_cells asegs m1 SQ [CB 56 jq] ->
  rw_cells asegs m1 ff [CB 120 fj; C8 ffp] -> rw_cells asegs m1 (2147450880 + ff / 8) [CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  amem ff 128 -> ff + 128 <= alloc_ceiling -> ff mod 128 = 0 ->
  pol P lo (SQ + 56) -> pol P ff (ff + 128) -> pol P (2147450880 + ff / 8) (2147450880 + ff / 8 + 16) ->
  evtA asegs P (fun ms' => exists (jq0 jq1 j1 : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AAL_RET2) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 AFA_DESCR) (Z_to_bv 64 AY_ALLOC) a3 a4 a5 a6 a7
                   (Z_to_bv 64 ff) s3 (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 56)) (Z_to_bv 64 ff) s7 s8 (Z_to_bv 64 2147450880) s10 (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
               F (Z_to_bv 64 AY_SET_DEFAULT) fc None m' (seg_rom asegs)
      /\ munch [(SQ, SQ + 56); (ff, ff + 128); (ff / 8 + 2147450880, ff / 8 + 2147450880 + 16)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo SQ
      /\ rw_cells asegs m' SQ [CB 16 jq0; C8 (Z_to_bv 64 (ff + 48)); CB 24 jq1; C8 (Z_to_bv 64 ff)]
      /\ rw_cells asegs m' ff [C8 (Z_to_bv 64 AFA_MAGIC); C8 (Z_to_bv 64 AFA_DESCR); C8 (Z_to_bv 64 AY_ALLOC); CB 96 j1; C8 ffp]
      /\ rw_cells asegs m' (ff / 8 + 2147450880)
           [C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 241); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0);
            C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); C1 (Z_to_bv 8 243); CB 4 (repeat (Z_to_bv 8 0) 4)]
      /\ length jq0 = 16%nat /\ length jq1 = 24%nat /\ length j1 = 96%nat)
    (MS (mkR (Z_to_bv 64 AAL_RET1) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 ff) a1 a2 a3 a4 a5 a6 a7
             s2 s3 (Z_to_bv 64 0) s5 s6 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AAL_RET1) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until ffp. intros ST MI CEIL LOQ SQH SQ32 FR FFC FSH FF1 FF2 FF3 PSTK PFF PFFS.
  unfold pol, AAL_RET1, AAL_RET2, AY_SET_DEFAULT, AY_ALLOC, AFA_MAGIC, AFA_DESCR, amem in *.
  assert (LFJ : length fj = 120%nat) by (destruct FFC as [[WF _] _]; cbn in WF; tauto).
  assert (LJQ : length jq = 56%nat) by (destruct FR as [[WF _] _]; cbn in WF; tauto).
  set (SHF := ff / 8 + 2147450880) in *. replace (2147450880 + ff / 8) with SHF in FSH, PFFS by lia.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 16 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(SQ, SQ + 56); (ff, ff + 128); (SHF, SHF + 16)] m1) as MU.
  pose proof (wmono_refl asegs m1) as WM.
  stepA. stepA. stepA.                                    (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; lia].   (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  shadow_addr.
  do 3 zstepA.                                            (* [comment removed for export] *)
  zstepA. zstepA. zstepA.                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. change (ff / 8 + 2147450880) with SHF.          (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [| exfalso; revert K1; rewrite ?unsigned_lit by lia; lia].   (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. stepA.                                          (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  apply evtA_done.
  lazymatch goal with H : rw_cells asegs ?mx SQ [CB 16 ?q0; _; CB 24 ?q1; _] |- _ =>
    eexists q0, q1, (skipn 8 (skipn 8 (skipn 8 fj))), mx end. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
  split; [lazymatch goal with H : rw_cells asegs _ SQ _ |- _ => exact H end|].
  split; [lazymatch goal with H : rw_cells asegs _ ff _ |- _ => exact H end|].
  split; [lazymatch goal with H : rw_cells asegs _ SHF _ |- _ => exact H end|].
  repeat first [rewrite length_firstn | rewrite length_skipn]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aal3_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s7 s8 s10 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ ff lo : Z) (jq0 jq1 : list byte) (shA : list byte),
  stk asegs m1 lo SQ -> mem_inv asegs m1 -> alloc_ceiling <= lo -> lo + 1024 <= SQ -> SQ + 192 <= 2^47 ->
  rw_cells asegs m1 SQ [CB 16 jq0; C8 (Z_to_bv 64 (ff + 48)); CB 24 jq1; C8 (Z_to_bv 64 ff)] ->
  rw_cells asegs m1 (ff + 32) [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  u8arr asegs m1 (2147450880 + (ff + 32) / 8) shA -> shA = blk_shadow 32 ->
  amem ff 128 -> ff + 128 <= alloc_ceiling -> ff mod 128 = 0 ->
  pol P lo (SQ + 56) -> pol P ff (ff + 128) -> pol P (2147450880 + ff / 8) (2147450880 + ff / 8 + 16) ->
  evtA asegs P (fun ms' => exists (k0 : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AAL_RET3) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 0) (Z_to_bv 64 104) (Z_to_bv 64 AY_MALLOC_W) a3 a4 a5 a6 a7
                   (Z_to_bv 64 ff) s3 (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 ((ff + 56) / 8 + 2147450880)) (Z_to_bv 64 ff) s7 s8 (Z_to_bv 64 2147450880) s10 (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
               F (Z_to_bv 64 AY_MALLOC_W) fc None m' (seg_rom asegs)
      /\ munch [(SQ, SQ + 56)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo SQ
      /\ rw_cells asegs m' SQ [CB 8 k0; C8 (Z_to_bv 64 (ff + 56)); C8 (Z_to_bv 64 (ff + 48)); CB 24 jq1; C8 (Z_to_bv 64 ff)]
      /\ length k0 = 8%nat)
    (MS (mkR (Z_to_bv 64 AAL_RET2) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 ff) s3 (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 (ff + 56)) (Z_to_bv 64 ff) s7 s8 (Z_to_bv 64 2147450880) s10 (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 AAL_RET2) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until shA. intros ST MI CEIL LOQ SQH FR YAF ASH ASHeq FF1 FF2 FF3 PSTK PFF PFFS.
  unfold pol, AAL_RET2, AAL_RET3, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W, amem in *.
  assert (LJQ : length jq0 = 16%nat /\ length jq1 = 24%nat) by (destruct FR as [[WF _] _]; cbn in WF; tauto).
  pose proof (blk_shadow_length 32 ltac:(lia)) as ASHlen. rewrite <- ASHeq in ASHlen.
  assert (A8 : (ff + 32) mod 8 = 0) by (clear -CEILB FF3; Z.div_mod_to_equations; lia).
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(SQ, SQ + 56)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  shadow_fast ASH (ff + 32) 8.                            (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. shadow_addr. zstepA.                            (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    pose proof (block_shadow_read0_u asegs mx 2147450880 (ff + 32) 32 (ff + 56) 8 ltac:(lia) ltac:(lia) ltac:(rewrite <- ASHeq; exact ASH) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as HR end.
  zstepA. clear HR. rewrite ?zxb_small, ?sxb_small by lia.   (* [comment removed for export] *)
  zstepA. if_false.                                       (* [comment removed for export] *)
  zstepA. zstepA. stepA.                                  (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  apply evtA_done. lazymatch goal with H : rw_cells asegs ?mx SQ [CB 8 ?k0; _; _; _; _] |- _ =>
    exists k0, mx; split; [reflexivity|];
    split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [assumption|]; split; [exact H|] end.
  repeat first [rewrite length_firstn | rewrite length_skipn]. lia.
Qed.
End RC__2.
