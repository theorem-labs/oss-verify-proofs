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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BYajlRep BYajl_iface BY_hand.
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
Definition AFZ_RET1 : Z := 0x81db8.   (* [comment removed for export] *)
Definition AFZ_RET2 : Z := 0x81e88.   (* [comment removed for export] *)
Definition AFZ_RET3 : Z := 0x81e98.   (* [comment removed for export] *)
Definition AFZ_J : Z := 0x81ea0.      (* [comment removed for export] *)
Definition AFZ_REL : Z := 0x81f00.    (* [comment removed for export] *)
Definition AFZ_MAGIC : Z := 0x41b58ab3.
Definition AFZ_DESCR : Z := 0x1ba79.
Definition AFZ_RETIRED : Z := 0x45e0360e.
Definition F1b : byte := Z_to_bv 8 241.
Definition F2b : byte := Z_to_bv 8 242.
Definition F3b : byte := Z_to_bv 8 243.
Definition F5b : byte := Z_to_bv 8 245.

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma afz1_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (T n lo : Z),
  stk bsegs m1 lo (bv_unsigned sp) -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo + 1024 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 ->
  rw_cells bsegs m1 677280 [C8 (Z_to_bv 64 714168)] -> rw_cells bsegs m1 714168 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells bsegs m1 677368 [C8 (Z_to_bv 64 714176)] -> rw_cells bsegs m1 714176 [C4 (Z_to_bv 64 1)] ->
  0 <= T < 2^64 -> 0 <= n < 2^64 ->
  pol P lo (bv_unsigned sp) -> pol P 0x10000 0x603000 ->
  evtA bsegs P (fun ms' => exists (SQ : Z) (jq : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AFZ_RET1) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 96) (Z_to_bv 64 714168) (sx32 (Z_to_bv 64 1)) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 n) (Z_to_bv 64 T) s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_STACK_MALLOC_1) fc None m' (seg_rom bsegs)
      /\ SQ mod 32 = 0 /\ bv_unsigned sp - 112 <= SQ <= bv_unsigned sp - 96
      /\ munch [(lo, bv_unsigned sp)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo SQ
      /\ rw_cells bsegs m' SQ [CB 16 jq]
      /\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
      /\ stk bsegs m' (SQ + 16) (bv_unsigned sp + -80))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 T) (Z_to_bv 64 n) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_FUZZ) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until lo. intros ST MI CEIL LOQ SPH SP16 G1 G2 G3 G4 R1 R2 PSTK PIMG. unfold AY_FUZZ, AFZ_RET1, AY_STACK_MALLOC_1, pol in *.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  carve_frame 96%nat ST.
  stepA. apply (rw_cells_split_CB bsegs _ _ [] 96 _ [] [8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  do 11 stepA.                                             (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  rewrite (unsigned_lit (bv_unsigned sp + -96)) by lia. rewrite (land_align32 (bv_unsigned sp + -96)) by lia.
  remember (bv_unsigned sp + -96 - (bv_unsigned sp + -96) mod 32) as SQ eqn:SQE.
  assert (SQF : SQ mod 32 = 0 /\ bv_unsigned sp - 112 <= SQ <= bv_unsigned sp - 96) by (subst SQ; clear -CEILB SP16; Z.div_mod_to_equations; lia).
  clear SQE.
  (* [comment removed for export] *)
  match type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
    apply (proj1 (ycells_app bsegs _ _ [c0; c1] rest)) in FR end.
  destruct FR as [FRlo SV]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV.
  pose proof (stk_release bsegs _ _ _ _ ST FRlo ltac:(lia)) as ST'. clear ST FRlo. cbn [cells_size csize Nat.add] in ST'.
  pose proof (proj2 (stk_split bsegs _ _ (SQ + 16) _ ST' ltac:(lia))) as GAP.
  destruct (stk_carve_at _ _ _ SQ 16 ST' ltac:(lia) ltac:(cbn; lia)) as [ST [jq FR]]. clear ST'.
  replace (bv_unsigned sp + -96 + Z.of_nat 16) with (bv_unsigned sp + -80) in SV, GAP by lia.
  stepA.                                                   (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
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
Lemma afz2_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ ff : Z) (jq fj : list byte) (ffp : word),
  mem_inv bsegs m1 -> alloc_ceiling <= SQ -> SQ + 112 <= 2^47 ->
  rw_cells bsegs m1 SQ [CB 16 jq] ->
  rw_cells bsegs m1 ff [CB 120 fj; C8 ffp] -> rw_cells bsegs m1 (2147450880 + ff / 8) [CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  amem ff 128 -> ff + 128 <= alloc_ceiling -> ff mod 128 = 0 ->
  pol P SQ (SQ + 16) -> pol P ff (ff + 128) -> pol P (2147450880 + ff / 8) (2147450880 + ff / 8 + 16) ->
  evtA bsegs P (fun ms' => exists (a4' a5' : word) (j1 j2 j3 : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AFZ_RET2) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 AY_CALLBACKS) (Z_to_bv 64 (ff + 64)) (Z_to_bv 64 0) (Z_to_bv 64 (ff + 32)) a4' a5' a6 a7
                   (Z_to_bv 64 ff) s3 s4 s5 (Z_to_bv 64 (ff / 8 + 2147450880)) (Z_to_bv 64 ff) (Z_to_bv 64 (-8)) s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AY_ALLOC) fc None m' (seg_rom bsegs)
      /\ munch [(SQ, SQ + 16); (ff, ff + 128); (ff / 8 + 2147450880, ff / 8 + 2147450880 + 16)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' SQ [CB 8 (firstn 8 jq); C8 (Z_to_bv 64 ff)]
      /\ rw_cells bsegs m' ff [C8 (Z_to_bv 64 AFZ_MAGIC); C8 (Z_to_bv 64 AFZ_DESCR); C8 (Z_to_bv 64 AY_FUZZ); CB 8 j1; C8 (Z_to_bv 64 0); CB 24 j2; C8 (Z_to_bv 64 4294967297); CB 48 j3; C8 ffp]
      /\ rw_cells bsegs m' (ff / 8 + 2147450880)
           [C1 F1b; C1 F1b; C1 F1b; C1 F1b; C1 (Z_to_bv 8 0); C1 F2b; C1 F2b; C1 F2b; C1 (Z_to_bv 8 0); C1 F3b; C1 F3b; C1 F3b; CB 4 (repeat (Z_to_bv 8 0) 4)]
      /\ length j1 = 8%nat /\ length j2 = 24%nat /\ length j3 = 48%nat)
    (MS (mkR (Z_to_bv 64 AFZ_RET1) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 ff) a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 (Z_to_bv 64 2147450880) s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFZ_RET1) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until ffp. intros MI SQL SQH FR FFC FSH FF1 FF2 FF3 PSTK PFF PFFS.
  unfold pol, AFZ_RET1, AFZ_RET2, AY_ALLOC, AY_FUZZ, AFZ_MAGIC, AFZ_DESCR, AY_CALLBACKS, F1b, F2b, F3b, amem in *.
  assert (LFJ : length fj = 120%nat) by (destruct FFC as [[WF _] _]; cbn in WF; tauto).
  assert (LJQ : length jq = 16%nat) by (destruct FR as [[WF _] _]; cbn in WF; tauto).
  set (SHF := ff / 8 + 2147450880) in *. replace (2147450880 + ff / 8) with SHF in FSH, PFFS by lia.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 16 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  pose proof (munch_refl [(SQ, SQ + 16); (ff, ff + 128); (SHF, SHF + 16)] m1) as MU.
  pose proof (wmono_refl bsegs m1) as WM.
  apply (rw_cells_split_CB bsegs _ _ [] 120 _ [_] [8; 8; 8; 8; 8; 24; 8; 48]%nat) in FFC; [| reflexivity]. cbn [app mk_CB_cells] in FFC.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [8; 8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  stepA. stepA. stepA.                                    (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; lia].   (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  do 3 zstepA.                                            (* [comment removed for export] *)
  zstepA. shadow_addr.                                    (* [comment removed for export] *)
  zstepA. change (ff / 8 + 2147450880) with SHF.          (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA. zstepA. zstepA.                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 3 zstepA.                                            (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  apply evtA_done.
  lazymatch goal with |- exists a4' a5' j1 j2 j3 m', MS _ _ _ _ _ ?mx _ = _ /\ _ =>
    lazymatch goal with H1 : rw_cells bsegs mx ff [_; _; _; CB 8 ?x1; _; CB 24 ?x2; _; CB 48 ?x3; _] |- _ =>
      eexists _, _, x1, x2, x3, mx end end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [lazymatch goal with H : rw_cells bsegs _ SQ _ |- _ => exact H end|].
  split; [lazymatch goal with H : rw_cells bsegs _ ff _ |- _ => exact H end|].
  split; [lazymatch goal with H : rw_cells bsegs _ SHF _ |- _ => exact H end|].
  rewrite !length_firstn, !length_skipn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma afz3_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ H T n : Z),
  mem_inv bsegs m1 -> 0 < H < 2^64 -> 0 <= n < 2^31 ->
  evtA bsegs P (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFZ_RET3) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 H) (Z_to_bv 64 T) (Z_to_bv 64 n) a3 a4 a5 a6 a7
                   s2 (Z_to_bv 64 n) (Z_to_bv 64 T) (Z_to_bv 64 H) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AY_PARSE) fc None m1 (seg_rom bsegs))
    (MS (mkR (Z_to_bv 64 AFZ_RET2) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 H) a1 a2 a3 a4 a5 a6 a7
             s2 (Z_to_bv 64 n) (Z_to_bv 64 T) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFZ_RET2) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until n. intros MI HR NR. unfold AFZ_RET2, AFZ_RET3, AY_PARSE.
  stepA.                                                  (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  replace (Z_to_bv 64 (bv_swrap 32 (n + 0))) with (Z_to_bv 64 n)
    by (rewrite Z.add_0_r, ybv_swrap32_eq; rewrite Z.mod_small by lia; f_equal; lia).
  stepA. stepA.                                           (* [comment removed for export] *)
  apply evtA_done. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma afz4_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ : Z),
  mem_inv bsegs m1 ->
  evtA bsegs P (fun ms' => ms' = MS (mkR (Z_to_bv 64 AFZ_J) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) s5 a1 a2 a3 a4 a5 a6 a7
                   s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AY_FREE) fc None m1 (seg_rom bsegs))
    (MS (mkR ra (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFZ_RET3) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros. unfold AFZ_RET3, AFZ_J, AY_FREE.
  stepA. stepA. apply evtA_done. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sh16_f5' : list cell := [C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b; C1 F5b].

Lemma afz5_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ ff PF : Z) (shf : list byte) (w0 : word),
  mem_inv bsegs m1 ->
  rw_cells bsegs m1 (ff / 8 + 2147450880) [CB 16 shf] ->
  rw_cells bsegs m1 ff [C8 w0] -> rw_cells bsegs m1 (ff + 120) [C8 (Z_to_bv 64 PF)] ->
  amem ff 128 -> ff + 128 <= alloc_ceiling -> ff mod 128 = 0 -> 0 <= PF < 2^64 ->
  pol P ff (ff + 128) -> pol P (ff / 8 + 2147450880) (ff / 8 + 2147450880 + 16) ->
  evtA bsegs P (fun ms' => exists (m' : mem),
      ms' = MS (mkR ra (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 PF) a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 ff) s3 s4 s5 (Z_to_bv 64 (ff / 8 + 2147450880)) (Z_to_bv 64 ff) (Z_to_bv 64 (-8)) s9 s10 s11 t3 t4 t5 t6)
               F (Z_to_bv 64 AFZ_REL) fc None m' (seg_rom bsegs)
      /\ munch [(ff / 8 + 2147450880, ff / 8 + 2147450880 + 16); (ff, ff + 8)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' (ff / 8 + 2147450880) sh16_f5'
      /\ rw_cells bsegs m' ff [C8 (Z_to_bv 64 AFZ_RETIRED)] /\ rw_cells bsegs m' (ff + 120) [C8 (Z_to_bv 64 PF)])
    (MS (mkR ra (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 ff) s3 s4 s5 (Z_to_bv 64 (ff / 8 + 2147450880)) (Z_to_bv 64 ff) (Z_to_bv 64 (-8)) s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFZ_J) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until w0. intros MI SHC FF0 FFP FF1 FF2 FF3 PFR PFF PFFS.
  unfold pol, AFZ_J, AFZ_REL, sh16_f5', F5b, AFZ_RETIRED, amem in *.
  assert (LS : length shf = 16%nat) by (destruct SHC as [[WF _] _]; cbn in WF; tauto).
  set (SHF := ff / 8 + 2147450880) in *.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 16 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(SHF, SHF + 16); (ff, ff + 8)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  apply (rw_cells_split_CB bsegs _ _ [] 16 _ [] [1;1;1;1;1;1;1;1;1;1;1;1;1;1;1;1]%nat) in SHC; [| reflexivity]. cbn [app mk_CB_cells] in SHC.
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { kill K0. }          (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 16 zstepA.                                           (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  apply evtA_done. lazymatch goal with |- exists m', MS _ _ _ _ _ ?mx _ = _ /\ _ => exists mx end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [lazymatch goal with H2 : rw_cells bsegs _ SHF _ |- _ => exact H2 end|].
  split; [lazymatch goal with H2 : rw_cells bsegs _ ff _ |- _ => exact H2 end| exact FFP].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma afz6_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (vra vs0 vs1 vs2 vs3 vs4 vs5 vs6 vs7 vs8 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ PF : Z) (fl : byte),
  mem_inv bsegs m1 ->
  rw_cells bsegs m1 PF [C1 fl] ->
  rw_cells bsegs m1 (bv_unsigned sp + -80) [C8 vs8; C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra] ->
  amem PF 1 -> PF + 1 <= alloc_ceiling -> alloc_ceiling + 96 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  P (Z_to_bv 64 PF, 1%nat) -> pol P (bv_unsigned sp - 96) (bv_unsigned sp) ->
  evtA bsegs P (fun ms' => exists (m' : mem),
      ms' = MS (mkR vra sp gp tp t0 t1 t2 vs0 vs1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 vs2 vs3 vs4 vs5 vs6 vs7 vs8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom bsegs)
      /\ munch [(PF, PF + 1)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ rw_cells bsegs m' PF [C1 (Z_to_bv 8 0)]
      /\ rw_cells bsegs m' (bv_unsigned sp + -80) [C8 vs8; C8 vs7; C8 vs6; C8 vs5; C8 vs4; C8 vs3; C8 vs2; C8 vs1; C8 vs0; C8 vra])
    (MS (mkR ra (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 PF) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AFZ_REL) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until fl. intros MI PFC SV PF1 PF2 SPL SPH PPF PSTK.
  unfold pol, AFZ_REL, amem in *.
  pose proof (bv_unsigned_in_range 64 sp) as SR. unfold bv_modulus in SR. cbn in SR.
  pose proof (munch_refl [(PF, PF + 1)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  assert (PPF' : forall a k, PF <= a -> a + Z.of_nat k <= PF + 1 -> (a = PF /\ k = 1%nat) -> P (Z_to_bv 64 a, k)) by (intros a k _ _ [-> ->]; exact PPF).
  zstepA.                                                 (* [comment removed for export] *)
  stepA. stepA.                                           (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 10 zstepA.                                           (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  replace (bv_unsigned sp + -96 + 96) with (bv_unsigned sp) by lia. rewrite ?Z_to_bv_bv_unsigned.
  stepA.                                                  (* [comment removed for export] *)
  apply evtA_done. lazymatch goal with |- exists m', MS _ _ _ _ _ ?mx _ = _ /\ _ => exists mx end.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|].
  split; [lazymatch goal with H2 : rw_cells bsegs _ PF _ |- _ => exact H2 end| lazymatch goal with H2 : rw_cells bsegs _ (bv_unsigned sp + -80) _ |- _ => exact H2 end].
Qed.
End RC__2.
