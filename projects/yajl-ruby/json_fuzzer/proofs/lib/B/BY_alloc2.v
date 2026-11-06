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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BI_shadow BI_globals2 BI_region_is_poisoned BI_asan_memcpy1 BI_asan_memcpy BYajlRep BYajl_iface BY_hand BY_alloc1.
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
Definition AAL_RET4 : Z := 0x8259c.   (* [comment removed for export] *)

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition afs_win : list byte := [Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 241; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0; Z_to_bv 8 0].

Lemma afs_window : forall m ff, ff mod 128 = 0 -> 0 <= ff ->
  bytes_at bsegs m (ff / 8 + 2147450880) afs_win ->
  shadow_window bsegs m 2147450880 (ff + 32) 32 afs_win /\ range_clean 2147450880 (ff + 32) 32 afs_win
  /\ shw_lo 2147450880 (ff + 32) = ff / 8 + 2147450880 /\ shw_hi 2147450880 (ff + 32) 32 = ff / 8 + 2147450880 + 8.
Proof. aceil.
  intros m ff A128 F0 BA.
  assert (E1 : shw_lo 2147450880 (ff + 32) = ff / 8 + 2147450880).
  { unfold shw_lo, al8. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear BA. Z.div_mod_to_equations. lia. }
  assert (E2 : shw_hi 2147450880 (ff + 32) 32 = ff / 8 + 2147450880 + 8).
  { unfold shw_hi, al8. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8. clear BA. Z.div_mod_to_equations. lia. }
  split; [| split; [| auto]].
  - split; [rewrite E1; exact BA| rewrite E1, E2; change (Z.of_nat (length afs_win)) with 8; lia].
  - intros g Hg. rewrite !Z.shiftr_div_pow2 in Hg by lia. change (2^3) with 8 in Hg.
    assert (GR : ff / 8 + 4 <= g <= ff / 8 + 7) by (clear BA E1 E2; Z.div_mod_to_equations; lia).
    exists (Z_to_bv 8 0). split; [| left; reflexivity]. rewrite E1.
    replace (Z.to_nat (2147450880 + g - (ff / 8 + 2147450880))) with (4 + Z.to_nat (g - ff / 8 - 4))%nat by lia.
    unfold afs_win. destruct (Z.to_nat (g - ff / 8 - 4)) as [|[|[|[|k]]]] eqn:EK; try reflexivity. exfalso. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aal4_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s3 s8 s9 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ ff lo H CBK CFGP CX : Z) (k0 jq1 hj : list byte) (shH shC wsD : list byte),
  stk bsegs m1 lo SQ -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo + 2224 <= SQ -> SQ + 192 <= 2^47 ->
  rw_cells bsegs m1 SQ [CB 8 k0; C8 (Z_to_bv 64 (ff + 48)); C8 (Z_to_bv 64 CBK); C8 (Z_to_bv 64 CX); CB 16 jq1; C8 (Z_to_bv 64 ff)] ->
  rw_cells bsegs m1 (ff + 32) [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  bytes_at bsegs m1 (ff / 8 + 2147450880) afs_win ->
  amem ff 128 -> ff + 128 <= alloc_ceiling -> ff mod 128 = 0 ->
  (* [comment removed for export] *)
  rw_cells bsegs m1 H [CB 104 hj] -> u8arr bsegs m1 (2147450880 + H / 8) shH -> shH = blk_shadow 104 ->
  17594333495296 <= H -> H + 104 <= alloc_ceiling -> H mod 16 = 0 -> (H + 104 <= ff \/ ff + 128 <= H) ->
  shadow_window bsegs m1 2147450880 (H + 72) 32 wsD -> range_clean 2147450880 (H + 72) 32 wsD -> shw_hi 2147450880 (H + 72) 32 <= 17594333495296 ->
  icp_globals bsegs m1 2147450880 ->
  (* [comment removed for export] *)
  rw_cells bsegs m1 CFGP [C4 (Z_to_bv 64 1); C4 (Z_to_bv 64 1)] -> u8arr bsegs m1 (2147450880 + CFGP / 8) shC -> shC = blk_shadow 8 ->
  amem CFGP 8 -> CFGP + 8 <= alloc_ceiling -> CFGP mod 8 = 0 -> (CFGP + 8 <= H \/ H + 104 <= CFGP) ->
  0 <= CBK < 2^64 -> 0 <= CX < 2^64 ->
  pol P lo (SQ + 56) -> pol P 0x10000 0x603000 -> pol P ff (ff + 128) -> pol P (2147450880 + ff / 8) (2147450880 + ff / 8 + 16) ->
  pol P H (H + 104) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) -> pol P (shw_lo 2147450880 (H + 72)) (shw_hi 2147450880 (H + 72) 32) ->
  pol P CFGP (CFGP + 8) -> pol P (2147450880 + CFGP / 8) (2147450880 + CFGP / 8 + 1) ->
  evtA bsegs P (fun ms' => exists (t0' t1' t2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (hj' : list byte) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AAL_RET4) (Z_to_bv 64 SQ) gp tp t0' t1' t2' sp (Z_to_bv 64 SQ) (Z_to_bv 64 (H + 72)) (sx32 (Z_to_bv 64 1)) (sx32 (Z_to_bv 64 1)) a3' a4' a5' a6' a7'
                   (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 CFGP) (Z_to_bv 64 (H + 72)) s9 (Z_to_bv 64 (ff + 56)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3' t4' t5' t6')
               F (Z_to_bv 64 AY_LEX_ALLOC) fc None m' (seg_rom bsegs)
      /\ munch [(SQ - 2224, SQ + 56); (H, H + 104)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo SQ
      /\ rw_cells bsegs m' SQ [CB 8 k0; C8 (Z_to_bv 64 (ff + 48)); C8 (Z_to_bv 64 CBK); C8 (Z_to_bv 64 CX); CB 16 jq1; C8 (Z_to_bv 64 ff)]
      /\ rw_cells bsegs m' H [C8 (Z_to_bv 64 CBK); C8 (Z_to_bv 64 CX); CB 56 hj']
      /\ rw_cells bsegs m' (H + 72) [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)]
      /\ length hj' = 56%nat
      /\ u8arr bsegs m' (2147450880 + H / 8) shH /\ bytes_at bsegs m' (ff / 8 + 2147450880) afs_win /\ icp_globals bsegs m' 2147450880)
    (MS (mkR (Z_to_bv 64 AAL_RET3) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 H) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 ff) s3 (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 CFGP) s8 s9 (Z_to_bv 64 (ff + 56)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 AAL_RET3) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until wsD. intros ST MI CEIL LOQ SQH FR YAF AW FF1 FF2 FF3 HC HS HSeq HR1 HR2 H16 SEPHF SWD RCD WDH IG CFC CSH CSHeq CR1 CR2 CF8 SEPCH CBR CXR
         PSTK PIMG PFF PFFS PH PHS PWD PC PCS.
  unfold pol, AAL_RET3, AAL_RET4, AY_LEX_ALLOC, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W, amem in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as HSlen. rewrite <- HSeq in HSlen.
  pose proof (blk_shadow_length 8 ltac:(lia)) as CSlen. rewrite <- CSHeq in CSlen.
  assert (H8 : H mod 8 = 0) by lia.
  assert (LHJ : length hj = 104%nat) by (destruct HC as [[WF _] _]; cbn in WF; tauto).
  assert (LJQ : length k0 = 8%nat /\ length jq1 = 16%nat) by (destruct FR as [[WF _] _]; cbn in WF; tauto).
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  assert (SHFR : 2147450880 <= ff / 8 + 2147450880 /\ ff / 8 + 2147450880 + 16 <= 17594333495296) by (clear -CEILB FF1 FF2; Z.div_mod_to_equations; lia).
  assert (SHHR : 2147450880 <= 2147450880 + H / 8 /\ 2147450880 + H / 8 + 13 <= 17594333495296) by (clear -CEILB HR1 HR2; Z.div_mod_to_equations; lia).
  assert (SHCR : 2147450880 <= 2147450880 + CFGP / 8 /\ 2147450880 + CFGP / 8 + 1 <= 17594333495296) by (clear -CEILB CR1 CR2; Z.div_mod_to_equations; lia).
  pose proof (shw_geom 2147450880 (H + 72) 32 ltac:(lia) ltac:(lia) ltac:(lia)) as GEOD. cbv zeta in GEOD.
  pose proof (munch_refl [(SQ - 2224, SQ + 56); (H, H + 104)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  unfold afs_win in *.
  zstepA. if_cases K0; zify_cond K0. { kill K0. }          (* [comment removed for export] *)
  stepA.                                                  (* [comment removed for export] *)
  zstepA. ugd.                                            (* [comment removed for export] *)
  zstepA. stepA. stepA. stepA.                            (* [comment removed for export] *)
  (* [comment removed for export] *)
  apply (rw_cells_split_CB bsegs _ _ [] 104 _ [] [72; 32]%nat) in HC; [| reflexivity]. cbn [app mk_CB_cells] in HC.
  apply (proj1 (ycells_app bsegs _ _ [_] [_])) in HC. destruct HC as [HC1 HC2]. cbn [cells_size csize Nat.add] in HC2.
  pose proof (rw_cells_bytes_at _ _ _ _ YAF) as SRCB. cbn [cells_bytes cbytes] in SRCB.
  stepA.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (IGx : icp_globals bsegs mx 2147450880) by (eapply icp_globals_transport; [exact IG| exact MU| exact WM| cbv [disjoint_from fst snd]; lia]);
    destruct (afs_window mx ff FF3 ltac:(lia) ltac:(assumption)) as (SWS & RCS & EWL & EWH);
    destruct SWD as [SWB SWL];
    pose proof (bytes_at_transport bsegs _ m1 mx _ _ SWB MU ltac:(cbv [disjoint_from fst snd]; lia)) as SWBx;
    assert (SWDx : shadow_window bsegs mx 2147450880 (H + 72) 32 wsD) by (split; [exact SWBx| exact SWL]) end.
  call_spA (asan_memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (H + 72) (ff + 32) 32 2147450880 _ afs_win wsD _ lo).
  all: rewrite ?USQ.
  - exact ST.
  - aceil; lia.
  - lia.
  - assumption.
  - reflexivity. - reflexivity. - reflexivity.
  - lia.
  - unfold range_in_mem, A_HIGHEND_VAL. clear -CEILB FF1 FF2. lia.
  - unfold range_in_mem, A_HIGHEND_VAL. right. lia.
  - lia. - lia. - lia.
  - left. lia.
  - left. lia.
  - right. lia.
  - exact HC2.
  - exact SRCB.
  - reflexivity.
  - exact IGx.
  - exact SWS.
  - exact RCS.
  - rewrite EWH. clear -CEILB FF1 FF2 HR1. lia.
  - exact SWDx.
  - exact RCD.
  - left. lia.
  - intros a k Ha Hk. apply PSTK; lia.
  - exact PIMG.
  - intros a k Ha Hk. apply PFF; lia.
  - intros a k Ha Hk. apply PH; lia.
  - rewrite EWL, EWH. intros a k Ha Hk. apply PFFS; lia.
  - exact PWD.
  - lazymatch goal with H : rw_cells bsegs _ (H + 72) _ |- _ => rename H into DST2 end.
    lazymatch goal with H : stk bsegs _ lo _ |- _ => rename H into ST2 end.
    lazymatch goal with H : icp_globals bsegs _ _ |- _ => rename H into IG2 end.
    lazymatch goal with H : shadow_window bsegs _ _ (ff + 32) _ _ |- _ => destruct H as [AW2 _] end.
    rewrite EWL in AW2. unfold afs_win in AW2.
    eapply rw_cells_reshape with (cs' := [C8 (Z_to_bv 64 535580); C8 (Z_to_bv 64 535600); C8 (Z_to_bv 64 535592); C8 (Z_to_bv 64 0)]) in DST2; [| cbn; repeat split; exact I| reflexivity| reflexivity].
    rewrite USQ in ST2.
    (* [comment removed for export] *)
    zstepA. if_cases K1; zify_cond K1. { kill K1. }        (* [comment removed for export] *)
    zstepA. ugd.                                          (* [comment removed for export] *)
    shadow_fast CSH CFGP 4.                               (* [comment removed for export] *)
    zstepA. zstepA. shadow_addr. zstepA.                  (* [comment removed for export] *)
    lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      pose proof (block_shadow_read0_u bsegs mx 2147450880 CFGP 8 (CFGP + 4) 4 ltac:(lia) ltac:(lia) ltac:(rewrite <- CSHeq; exact CSH) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(clear -CEILB CF8; Z.div_mod_to_equations; lia)) as HR end.
    zstepA. clear HR. rewrite ?zxb_small, ?sxb_small by lia.   (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA. if_false.                                     (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    stepA.                                                (* [comment removed for export] *)
    (* [comment removed for export] *)
    shadow_fast HS H 8.                                   (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA. shadow_fast HS (H + 8) 8.                     (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    stepA. stepA.                                         (* [comment removed for export] *)
    apply evtA_done. lazymatch goal with H1 : rw_cells bsegs ?mx H [_; _; CB 56 ?hjx] |- _ =>
      lazymatch goal with H2 : rw_cells bsegs mx SQ _ |- _ =>
      eexists _, _, _, _, _, _, _, _, _, _, _, _, hjx, mx; split; [reflexivity|];
      split; [exact MU|]; split; [exact WM|]; split; [assumption|]; split; [exact ST2|];
      split; [exact H2|];
      split; [exact H1|]; split; [exact DST2|]; split; [repeat first [rewrite length_firstn | rewrite length_skipn]; lia|];
      split; [assumption|]; split; [exact AW2| eapply icp_globals_transport; [exact IG| exact MU| exact WM| cbv [disjoint_from fst snd]; lia]] end end.
Qed.
End RC__2.
