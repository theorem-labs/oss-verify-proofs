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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BYajlRep BYajl_iface BY_rz BY_hand BY_parse_kit.
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
Definition AY_PRO_RET : Z := 0x87b1c.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pro1_seg : forall (P : acc -> Prop) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (H T len lo : Z),
  stk bsegs m1 lo (bv_unsigned sp) -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo + 1024 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  bv_unsigned sp mod 16 = 0 ->
  rw_cells bsegs m1 677280 [C8 (Z_to_bv 64 714168)] -> rw_cells bsegs m1 714168 [C8 (Z_to_bv 64 2147450880)] ->
  rw_cells bsegs m1 677368 [C8 (Z_to_bv 64 714176)] -> rw_cells bsegs m1 714176 [C4 (Z_to_bv 64 1)] ->
  0 < H -> H + 104 <= alloc_ceiling -> 0 <= T < 2^64 -> 0 <= len < 2^64 ->
  pol P lo (bv_unsigned sp) -> pol P 0x10000 0x603000 ->
  evtA bsegs P (fun ms' => exists (SQ : Z) (jq1 jq2 : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AY_PRO_RET) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 96) (Z_to_bv 64 714168) (sx32 (Z_to_bv 64 1)) a3 a4 a5 a6 a7
                   (Z_to_bv 64 H) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x3e110) fc None m' (seg_rom bsegs)
      /\ SQ mod 32 = 0 /\ bv_unsigned sp - 368 <= SQ <= bv_unsigned sp - 352
      /\ munch [(lo, bv_unsigned sp)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo SQ /\ stk bsegs m' (SQ + 240) (bv_unsigned sp + -112)
      /\ rw_cells bsegs m' SQ [CB 176 jq1; C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 len); CB 48 jq2]
      /\ rw_cells bsegs m' (bv_unsigned sp + -112) [C8 (reg_get F 8); C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 H) (Z_to_bv 64 T) (Z_to_bv 64 len) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 AY_DO_PARSE) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until lo. intros ST MI CEIL LOQ SPH SP16 G1 G2 G3 G4 HR1 HR2 TR LR PSTK PIMG. unfold AY_DO_PARSE, AY_PRO_RET, pol in *.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  carve_frame 352%nat ST.
  stepA. apply (rw_cells_split_CB bsegs _ _ [] 352 _ [] [8;232;8;8;8;8;8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  do 15 stepA.                                             (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  rewrite (unsigned_lit (bv_unsigned sp + -352)) by lia. rewrite (land_align32 (bv_unsigned sp + -352)) by lia.
  remember (bv_unsigned sp + -352 - (bv_unsigned sp + -352) mod 32) as SQ eqn:SQE.
  assert (SQF : SQ mod 32 = 0 /\ bv_unsigned sp - 368 <= SQ <= bv_unsigned sp - 352) by (subst SQ; clear -CEILB SP16; Z.div_mod_to_equations; lia).
  clear SQE.
  (* [comment removed for export] *)
  apply (rw_cells_split_CB bsegs _ _ [C8 (Z_to_bv 64 0)] 232 _ _ [232]%nat) in FR; [| reflexivity]. cbn [app mk_CB_cells] in FR.
  match type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?rest) =>
    apply (proj1 (ycells_app bsegs _ _ [c0; c1] rest)) in FR end.
  destruct FR as [FRlo SV]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in SV.
  pose proof (stk_release bsegs _ _ _ _ ST FRlo ltac:(lia)) as ST'. clear ST FRlo. cbn [cells_size csize Nat.add] in ST'.
  destruct (stk_carve_at3 _ _ _ SQ 240 ST' ltac:(lia) ltac:(cbn; lia)) as (ST & [jq FR] & GAP). clear ST'.
  replace (bv_unsigned sp + -352 + Z.of_nat 240) with (bv_unsigned sp + -112) in SV, GAP by lia. change (Z.of_nat 240) with 240 in GAP.
  stepA.                                                   (* [comment removed for export] *)
  stepA. stepA.                                            (* [comment removed for export] *)
  do 4 stepA.                                              (* [comment removed for export] *)
  zstepA. zstepA.                                          (* [comment removed for export] *)
  stepA.                                                   (* [comment removed for export] *)
  zstepA. if_false.                                        (* [comment removed for export] *)
  stepA. stepA.                                            (* [comment removed for export] *)
  apply evtA_done. cbv beta. eexists SQ, _, _, _. split; [reflexivity|].
  split; [exact (proj1 SQF)|]. split; [exact (proj2 SQF)|].
  repeat match goal with |- _ /\ _ => split end; try assumption; exact FR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma pro2_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s4 s5 s6 s7 s8 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (H SQ ff lo : Z) (jq1 jq2 fj : list byte) (T len : Z) (ffp pew pad : word) (shH : list byte)
    (CBv CXv Lv bc DBv SBv sz used : Z),
  stk bsegs m1 lo SQ -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo + 1024 <= SQ -> SQ + 352 <= bv_unsigned sp -> bv_unsigned sp <= 2^47 ->
  SQ mod 32 = 0 ->
  rw_cells bsegs m1 SQ [CB 176 jq1; C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 len); CB 48 jq2] ->
  rw_cells bsegs m1 ff [CB 120 fj; C8 ffp] -> rw_cells bsegs m1 (2147450880 + ff / 8) [CB 16 (repeat (Z_to_bv 8 0) 16)] ->
  (6303744 <= ff /\ (ff + 128 <= 2147446784 \/ 17594333495296 <= ff)) -> ff + 128 <= alloc_ceiling -> ff mod 128 = 0 ->
  rw_cells bsegs m1 H [C8 (Z_to_bv 64 CBv); C8 (Z_to_bv 64 CXv); C8 (Z_to_bv 64 Lv); C8 pew; C4 (Z_to_bv 64 bc); C4 pad; C8 (Z_to_bv 64 DBv); C8 (Z_to_bv 64 SBv);
                       C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 used); C8 (Z_to_bv 64 (H + 72)); C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  0 < used < 2^31 ->
  17594333495296 <= H -> H + 104 <= alloc_ceiling -> H mod 16 = 0 ->
  (H + 104 <= ff \/ ff + 128 <= H) ->
  u8arr bsegs m1 (2147450880 + H / 8) shH -> shH = blk_shadow 104 ->
  pol P lo (bv_unsigned sp) -> pol P ff (ff + 128) -> pol P (2147450880 + ff / 8) (2147450880 + ff / 8 + 16) ->
  pol P H (H + 104) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) ->
  evtA bsegs P (fun ms' => exists (k0 k224 j1 j2 j3 : list byte) (obw olw : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AY_PRO_RET) (Z_to_bv 64 SQ) gp tp (Z_to_bv 64 9223372036854775809) (Z_to_bv 64 (H + 24)) (Z_to_bv 64 (H + 56))
                   sp (Z_to_bv 64 SQ) (Z_to_bv 64 used) (Z_to_bv 64 ((H + 16) / 8 + 2147450880)) (Z_to_bv 64 ((H + 56) / 8 + 2147450880)) (Z_to_bv 64 3)
                   (Z_to_bv 64 ((H + 24) / 8 + 2147450880)) (Z_to_bv 64 ((H + 8) / 8 + 2147450880)) (Z_to_bv 64 0x21c74) (Z_to_bv 64 (H / 8 + 2147450880))
                   (Z_to_bv 64 H) (Z_to_bv 64 ff) (Z_to_bv 64 (H + 48)) s5 (Z_to_bv 64 (H + 60)) (Z_to_bv 64 ((H + 48) / 8 + 2147450880)) (Z_to_bv 64 ((H + 60) / 8 + 2147450880))
                   (Z_to_bv 64 2147450880) (Z_to_bv 64 (H + 64)) (Z_to_bv 64 (ff / 8 + 2147450880)) (Z_to_bv 64 (H + 8)) (Z_to_bv 64 (H + 16)) t5 t6)
               F (Z_to_bv 64 AY_PHEAD) fc None m' (seg_rom bsegs)
      /\ munch [(SQ, SQ + 240); (ff, ff + 128); (ff / 8 + 2147450880, ff / 8 + 2147450880 + 16); (H + 32, H + 36)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo SQ
      /\ rw_cells bsegs m' SQ
           [CB 16 k0; C8 (Z_to_bv 64 0x21dc0); C8 (Z_to_bv 64 0x21d60); C8 (Z_to_bv 64 3); C8 (Z_to_bv 64 7); C8 (Z_to_bv 64 9223372036854775809);
            C8 (Z_to_bv 64 ((H + 32) / 8 + 2147450880)); C8 (Z_to_bv 64 0x21ba0); C8 (Z_to_bv 64 ff); C8 (Z_to_bv 64 (H + 40));
            C8 (Z_to_bv 64 ((H + 8) / 8 + 2147450880)); C8 (Z_to_bv 64 (H + 8)); C8 (Z_to_bv 64 ((H + 24) / 8 + 2147450880)); C8 (Z_to_bv 64 (H + 24));
            C8 (Z_to_bv 64 AY_JT_PTOK); C8 (Z_to_bv 64 (H / 8 + 2147450880)); C8 (Z_to_bv 64 H); C8 (Z_to_bv 64 ((H + 56) / 8 + 2147450880));
            C8 (Z_to_bv 64 (H + 56)); C8 (Z_to_bv 64 ((H + 16) / 8 + 2147450880)); C8 (Z_to_bv 64 (H + 16)); C8 (Z_to_bv 64 T); C8 (Z_to_bv 64 len);
            C8 (Z_to_bv 64 AY_JT_PSTATE); C8 (Z_to_bv 64 (H + 32)); C8 (Z_to_bv 64 (ff + 32)); C8 (Z_to_bv 64 (ff + 64)); CB 8 k224; C8 (Z_to_bv 64 ff)]
      /\ rw_cells bsegs m' H [C8 (Z_to_bv 64 CBv); C8 (Z_to_bv 64 CXv); C8 (Z_to_bv 64 Lv); C8 pew; C4 (Z_to_bv 64 0); C4 pad; C8 (Z_to_bv 64 DBv); C8 (Z_to_bv 64 SBv);
                           C4 (Z_to_bv 64 sz); C4 (Z_to_bv 64 used); C8 (Z_to_bv 64 (H + 72)); C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)]
      /\ rw_cells bsegs m' ff [C8 (Z_to_bv 64 AFF_MAGIC); C8 (Z_to_bv 64 AFF_DESCR); C8 (Z_to_bv 64 AY_DO_PARSE); CB 8 j1]
      /\ rw_cells bsegs m' (ff + 32) [C8 obw] /\ rw_cells bsegs m' (ff + 40) [CB 24 j2] /\ rw_cells bsegs m' (ff + 64) [C4 olw]
      /\ rw_cells bsegs m' (ff + 68) [CB 52 j3; C8 ffp]
      /\ rw_cells bsegs m' (ff / 8 + 2147450880) pffsh
      /\ length j1 = 8%nat /\ length j2 = 24%nat /\ length j3 = 52%nat)
    (MS (mkR (Z_to_bv 64 AY_PRO_RET) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 ff) a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 H) s3 s4 s5 s6 s7 s8 (Z_to_bv 64 2147450880) s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 AY_PRO_RET) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until used. intros ST MI CEIL LOQ SQH SPH SQ32 FR FFC FSH FF1 FF2 FF3 HC UR HR1 HR2 HR3 SEPHF SHH SHHeq PSTK PFF PFFS PH PHS.
  unfold pol, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W, AY_PRO_RET, AY_PHEAD, AY_JT_PSTATE, AY_JT_PTOK, AFF_MAGIC, AFF_DESCR, AY_DO_PARSE in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as SHHlen. rewrite <- SHHeq in SHHlen.
  assert (H8 : H mod 8 = 0) by lia.
  assert (LFJ : length fj = 120%nat) by (destruct FFC as [[WF _] _]; cbn in WF; tauto).
  set (SHF := ff / 8 + 2147450880) in *. replace (2147450880 + ff / 8) with SHF in FSH, PFFS by lia.
  assert (SHFR : 2147450880 <= SHF /\ SHF + 16 <= 17594333495296) by (subst SHF; Z.div_mod_to_equations; lia).
  pose proof (munch_refl [(SQ, SQ + 240); (ff, ff + 128); (SHF, SHF + 16); (H + 32, H + 36)] m1) as MU.
  pose proof (wmono_refl bsegs m1) as WM.
  stepA. stepA. stepA.                                    (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0; [| exfalso; revert K0; rewrite ?unsigned_lit by lia; lia].   (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 5 zstepA.                                            (* [comment removed for export] *)
  do 3 zstepA.                                            (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. shadow_addr. change (ff / 8 + 2147450880) with SHF.   (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  do 4 zstepA.                                            (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  ugd.                                                    (* [comment removed for export] *)
  zstepA. zstepA. ugd.                                    (* [comment removed for export] *)
  zstepA. zstepA.                                         (* [comment removed for export] *)
  zstepA. shadow_addr.                                    (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
  assert (SHR : ov_read_bytes bsegs mx (Z_to_bv 64 ((H + 32) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]) by
   (replace ((H + 32) / 8 + 2147450880) with (2147450880 + (H + 32) / 8) by lia;
    apply (block_shadow_read0_u bsegs mx 2147450880 H 104 (H + 32) 4); [lia| lia| rewrite <- SHHeq; exact SHH| lia| lia| lia| lia]) end.
  zstepA. clear SHR. rewrite ?zxb_small, ?sxb_small by lia.   (* [comment removed for export] *)
  zstepA. if_true.                                        (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. zstepA. shadow_addr. zstepA.                    (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
  assert (SHR : ov_read_bytes bsegs mx (Z_to_bv 64 ((H + 60) / 8 + 2147450880)) 1 = Some [Z_to_bv 8 0]) by
   (replace ((H + 60) / 8 + 2147450880) with (2147450880 + (H + 60) / 8) by lia;
    apply (block_shadow_read0_u bsegs mx 2147450880 H 104 (H + 60) 4); [lia| lia| rewrite <- SHHeq; exact SHH| lia| lia| lia| lia]) end.
  zstepA. clear SHR. rewrite ?zxb_small, ?sxb_small by lia.   (* [comment removed for export] *)
  zstepA. if_true.                                        (* [comment removed for export] *)
  zstepA. rewrite ?ysx32_small by lia.                    (* [comment removed for export] *)
  zstepA. if_cases K1; zify_cond K1; [| exfalso; revert K1; rewrite ?unsigned_lit by lia; lia].   (* [comment removed for export] *)
  do 10 zstepA.      (* [comment removed for export] *)
  do 10 zstepA.      (* [comment removed for export] *)
  do 40 (zstepA; try shadow_addr).
  (* [comment removed for export] *)
  rewrite (land7_mod (H + 56)) in * by lia. rewrite (land7_mod (H + 60)) in * by lia.
  replace ((H + 56) mod 8 + 3) with 3 in * by (clear -CEILB H8; Z.div_mod_to_equations; lia).
  replace ((H + 60) mod 8 + 3) with 7 in * by (clear -CEILB H8; Z.div_mod_to_equations; lia).
  lazymatch goal with H0 : rw_cells bsegs ?mx SHF ?cs |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H0 into FSH' end.
  lazymatch type of FSH' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?c10 :: ?c11 :: [CB 4 ?tl]) =>
    replace tl with (repeat (Z_to_bv 8 0) 4) in FSH' by reflexivity end.
  (* [comment removed for export] *)
  lazymatch goal with H0 : rw_cells bsegs ?mx ff ?cs |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H0 into FFC' end.
  apply (rw_cells_split_CB bsegs _ _ [_; _; _] 96 _ _ [8; 8; 24; 4; 52]%nat) in FFC'; [| reflexivity]. cbn [app mk_CB_cells] in FFC'.
  lazymatch type of FFC' with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?rest) =>
    apply (proj1 (ycells_app bsegs _ _ [c0; c1; c2; c3] rest)) in FFC' end.
  destruct FFC' as [FFA R1]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R1.
  lazymatch type of R1 with rw_cells _ _ _ (?c0 :: ?rest) => apply (proj1 (ycells_app bsegs _ _ [c0] rest)) in R1 end.
  destruct R1 as [FOB R2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R2.
  lazymatch type of R2 with rw_cells _ _ _ (?c0 :: ?rest) => apply (proj1 (ycells_app bsegs _ _ [c0] rest)) in R2 end.
  destruct R2 as [FJ2 R3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in R3.
  lazymatch type of R3 with rw_cells _ _ _ (?c0 :: ?rest) => apply (proj1 (ycells_app bsegs _ _ [c0] rest)) in R3 end.
  destruct R3 as [FOL FJ3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FJ3.
  replace (ff + 32 + 8) with (ff + 40) in FJ2 by lia. replace (ff + 32 + 8 + 24) with (ff + 64) in FOL by lia. replace (ff + 32 + 8 + 24 + 4) with (ff + 68) in FJ3 by lia.
  apply (acb8_c8_in _ _ [] []) in FOB. cbn [app] in FOB. apply (acb4_c4_in _ _ [] []) in FOL. cbn [app] in FOL.
  (* [comment removed for export] *)
  lazymatch goal with H0 : rw_cells bsegs ?mx SQ (CB 16 ?a :: ?rest) |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    remember a as k0 eqn:E1 in H0; clear E1;
    lazymatch rest with context [CB 8 ?b] => remember b as k224 eqn:E2 in H0; clear E2 end; rename H0 into FRf end.
  lazymatch type of FFA with rw_cells _ _ _ [_; _; _; CB 8 ?a] => assert (LJ1 : length a = 8%nat) by (rewrite ?length_firstn, ?length_skipn; lia); remember a as j1 eqn:E3 in FFA, LJ1; clear E3 end.
  lazymatch type of FJ2 with rw_cells _ _ _ [CB 24 ?a] => assert (LJ2 : length a = 24%nat) by (rewrite ?length_firstn, ?length_skipn; lia); remember a as j2 eqn:E4 in FJ2, LJ2; clear E4 end.
  lazymatch type of FJ3 with rw_cells _ _ _ [CB 52 ?a; _] => assert (LJ3 : length a = 52%nat) by (rewrite ?length_firstn, ?length_skipn; lia); remember a as j3 eqn:E5 in FJ3, LJ3; clear E5 end.
  lazymatch type of FOB with rw_cells _ _ _ [C8 ?w] => remember w as obw eqn:E6 in FOB; clear E6 end.
  lazymatch type of FOL with rw_cells _ _ _ [C4 ?w] => remember w as olw eqn:E7 in FOL; clear E7 end.
  apply evtA_done. cbv beta. exists k0, k224, j1, j2, j3, obw, olw. eexists. split; [reflexivity|].
  repeat match goal with |- _ /\ _ => split end; assumption.
Qed.
End RC__1.
