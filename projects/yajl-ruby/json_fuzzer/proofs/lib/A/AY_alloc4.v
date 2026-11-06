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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import InitMem SysStep Arr Cells.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import Prelim YajlBase YajlLeaf YajlBuf YajlLex YajlParser YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RYajlRep RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.A Require Import A_iface AI_shadow AI_globals2 AI_region_is_poisoned AI_asan_memset AYajlRep AYajl_iface AY_hand AY_alloc1 AY_alloc2 AY_alloc3.
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
Definition AAL_RET7 : Z := 0x827a8.   (* [comment removed for export] *)

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Lemma aal7_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s5v : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ ff lo H CBK CFGP CX L D : Z) (pew pad DBJ SBK SZ U YF : word) (shH wsS : list byte),
  stk asegs m1 lo SQ -> mem_inv asegs m1 -> alloc_ceiling <= lo -> lo + 2224 <= SQ -> SQ + 192 <= 2^47 ->
  rw_cells asegs m1 H (hcells15 CBK CX L pew (Z_to_bv 64 0) pad DBJ SBK SZ U YF) ->
  u8arr asegs m1 (2147450880 + H / 8) shH -> shH = blk_shadow 104 ->
  17594333495296 <= H -> H + 104 <= alloc_ceiling -> H mod 16 = 0 -> 0 <= ff < 2^47 -> 0 <= D < 2^64 ->
  shadow_window asegs m1 2147450880 (H + 48) 16 wsS -> range_clean 2147450880 (H + 48) 16 wsS -> shw_hi 2147450880 (H + 48) 16 <= 17594333495296 ->
  icp_globals asegs m1 2147450880 ->
  pol P lo (SQ + 56) -> pol P 0x10000 0x603000 ->
  pol P H (H + 104) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) -> pol P (shw_lo 2147450880 (H + 48)) (shw_hi 2147450880 (H + 48) 16) ->
  evtA asegs P (fun ms' => exists (t0' t1' t2' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
      ms' = MS (mkR (Z_to_bv 64 AAL_RET7) (Z_to_bv 64 SQ) gp tp t0' t1' t2' sp (Z_to_bv 64 SQ) (Z_to_bv 64 0) (Z_to_bv 64 0) (Z_to_bv 64 128) (Z_to_bv 64 AY_REALLOC_W) a4' a5' a6' a7'
                   (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (H + 48)) (Z_to_bv 64 (H + 64)) (Z_to_bv 64 ff) (Z_to_bv 64 CFGP) (Z_to_bv 64 CBK) (Z_to_bv 64 2147450880) (Z_to_bv 64 (H + 72)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3' t4' t5' t6')
               F (Z_to_bv 64 AY_REALLOC_W) fc None m' (seg_rom asegs)
      /\ munch [(SQ - 2224, SQ); (H, H + 104)] m1 m' /\ wmono asegs m1 m' /\ mem_inv asegs m'
      /\ stk asegs m' lo SQ
      /\ rw_cells asegs m' H (hcells15 CBK CX L pew (Z_to_bv 64 0) pad (Z_to_bv 64 D) (Z_to_bv 64 0) (Z_to_bv 64 128) (Z_to_bv 64 0) (Z_to_bv 64 (H + 72)))
      /\ u8arr asegs m' (2147450880 + H / 8) shH /\ icp_globals asegs m' 2147450880)
    (MS (mkR (Z_to_bv 64 AAL_RET5) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 D) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (ff + 32)) s5v (Z_to_bv 64 ff) (Z_to_bv 64 CFGP) (Z_to_bv 64 CBK) (Z_to_bv 64 2147450880) (Z_to_bv 64 (H + 72)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 AAL_RET5) fc None m1 (seg_rom asegs)).
Proof. aceil.
  intros until wsS. intros ST MI CEIL LOQ SQH HC HS HSeq HR1 HR2 H16 FFR DR SWS RCS WSH IG PSTK PIMG PH PHS PWS.
  unfold pol, AAL_RET5, AAL_RET7, AY_REALLOC_W, hcells15, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as HSlen. rewrite <- HSeq in HSlen.
  assert (H8 : H mod 8 = 0) by lia.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  assert (SHHR : 2147450880 <= 2147450880 + H / 8 /\ 2147450880 + H / 8 + 13 <= 17594333495296) by (clear -CEILB HR1 HR2; Z.div_mod_to_equations; lia).
  pose proof (shw_geom 2147450880 (H + 48) 16 ltac:(lia) ltac:(lia) ltac:(lia)) as GEOS. cbv zeta in GEOS.
  pose proof (munch_refl [(SQ - 2224, SQ); (H, H + 104)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
  zstepA. shadow_fast HS (H + 40) 8.                      (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. zstepA. stepA.                                  (* [comment removed for export] *)
  stepA. stepA.                                           (* [comment removed for export] *)
  (* [comment removed for export] *)
  lazymatch goal with HC1 : rw_cells asegs ?mx H ?cs |- _ =>
    apply (proj1 (ycells_app asegs _ _ (firstn 7 cs) (skipn 7 cs))) in HC1; cbn [firstn skipn] in HC1;
    destruct HC1 as [HCa HCb]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HCb;
    apply (proj1 (ycells_app asegs _ _ [_; _; _] (skipn 3 (skipn 7 cs)))) in HCb; cbn [firstn skipn] in HCb;
    destruct HCb as [HCm HCc]; cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in HCc end.
  eapply rw_cells_reshape with (cs' := [CB 16 (le8 SBK ++ le4 SZ ++ le4 U)]) in HCm;
    [| cbn [cells_wf cell_wf]; split; [rewrite !length_app, length_le8, !length_le4; reflexivity| exact I]
     | cbn [cells_bytes cbytes]; rewrite !app_nil_r, <- ?app_assoc; reflexivity | reflexivity].
  stepA.                                                  (* [comment removed for export] *)
  lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    assert (IGx : icp_globals asegs mx 2147450880) by (eapply icp_globals_transport; [exact IG| exact MU| exact WM| cbv [disjoint_from fst snd]; lia]);
    destruct SWS as [SWB SWL];
    pose proof (bytes_at_transport asegs _ m1 mx _ _ SWB MU ltac:(cbv [disjoint_from fst snd]; lia)) as SWBx;
    assert (SWSx : shadow_window asegs mx 2147450880 (H + 48) 16 wsS) by (split; [exact SWBx| exact SWL]) end.
  call_spA (asan_memset_small_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (H + 48) 0 16 2147450880 wsS _ lo).
  all: rewrite ?USQ.
  - exact ST.
  - aceil; lia.
  - lia.
  - assumption.
  - reflexivity. - reflexivity.
  - rewrite unsigned_lit by lia. reflexivity.
  - lia. - lia. - lia.
  - left. lia.
  - right. lia.
  - exact HCm.
  - exact IGx.
  - exact SWSx.
  - exact RCS.
  - left. lia.
  - intros a k Ha Hk. apply PSTK; lia.
  - exact PIMG.
  - intros a k Ha Hk. apply PH; lia.
  - exact PWS.
  - lazymatch goal with H1 : rw_cells asegs _ (H + 48) _ |- _ => rename H1 into DSTm end.
    lazymatch goal with H1 : stk asegs _ lo _ |- _ => rename H1 into ST2 end.
    lazymatch goal with H1 : icp_globals asegs _ _ |- _ => rename H1 into IG2 end.
    rewrite USQ in ST2.
    change (Z.to_nat 16) with 16%nat in DSTm. cbn [repeat] in DSTm.
    eapply rw_cells_reshape with (cs' := [C8 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]) in DSTm; [| cbn; repeat split; exact I| reflexivity| reflexivity].
    (* [comment removed for export] *)
    lazymatch type of HCa with rw_cells _ ?mx _ ?csa => lazymatch type of DSTm with rw_cells _ _ _ ?csm => lazymatch type of HCc with rw_cells _ _ _ ?csc =>
      assert (HC : rw_cells asegs mx H (csa ++ csm ++ csc))
        by (apply (proj2 (ycells_app asegs _ _ csa (csm ++ csc))); split; [exact HCa|]; cbn [cells_size csize Nat.add];
            apply (proj2 (ycells_app asegs _ _ csm csc)); split; [exact DSTm| cbn [cells_size csize Nat.add]; exact HCc]) end end end.
    clear HCa DSTm HCc. cbn [app] in HC.
    shadow_fast HS (H + 64) 8.                            (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    shadow_fast HS (H + 56) 4.                            (* [comment removed for export] *)
    stepA. zstepA.                                        (* [comment removed for export] *)
    zstepA.                                               (* [comment removed for export] *)
    shadow_fast HS (H + 80) 8.                            (* [comment removed for export] *)
    zstepA. shadow_fast HS (H + 96) 8.                    (* [comment removed for export] *)
    zstepA. zstepA. stepA.                                (* [comment removed for export] *)
    stepA.                                                (* [comment removed for export] *)
    apply evtA_done. lazymatch goal with |- exists _ _ _ _ _ _ _ _ _ _ _ m', MS _ _ _ _ _ ?mx _ = _ /\ _ =>
      eexists _, _, _, _, _, _, _, _, _, _, _, mx end.
    split; [reflexivity|].
    split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST2|].
    split; [exact HC|].
    split; [assumption|].
    eapply icp_globals_transport; [exact IG| exact MU| exact WM| cbv [disjoint_from fst snd]; lia].
Qed.
End RC__2.
