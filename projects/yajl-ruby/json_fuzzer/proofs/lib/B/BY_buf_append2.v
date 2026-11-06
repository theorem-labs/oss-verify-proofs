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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Agent Require Import MallocBlocks.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.MS Require Import MallocRep.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import RawAlloc Prelim YajlBase YajlLeaf YajlBuf YajlFactsBuf.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RY_lib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages LazyModel NodesA Shadow.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import B_iface BI_shadow BI_region_is_poisoned BI_asan_memcpy1 BI_asan_memcpy BYajlRep BYajl_iface BY_ubkit BY_rz BY_buf_append1.
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
Definition AAPP_COPY : Z := 0x87418.

(* [comment removed for export] *)
End RC__1.
Ltac shadow_reload BS E w :=
  let HR := fresh "SHR" in
  lazymatch goal with
  | |- evtA ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      lazymatch type of BS with
      | u8arr _ _ (?SB + ?A / 8) ?shb =>
          lazymatch goal with
          | Eshb : shb = blk_shadow ?n |- _ =>
              assert (HR : ov_read_bytes segs m (Z_to_bv 64 (SB + E / 8)) 1 = Some [Z_to_bv 8 0])
                by (apply (block_shadow_read0_u segs m SB A n E w); [lia| lia| rewrite <- Eshb; exact BS| lia| lia| lia| lia])
          end
      end
  end;
  zstepA; clear HR; rewrite ?zxb_small, ?sxb_small by lia; zstepA; if_false.
(* [comment removed for export] *)
Ltac shadow_reload2 BS E w :=
  let HR := fresh "SHR" in
  lazymatch goal with
  | |- evtA ?segs _ _ (MS _ _ _ _ _ ?m _) =>
      lazymatch type of BS with
      | u8arr _ _ (?SB + ?A / 8) ?shb =>
          lazymatch goal with
          | Eshb : shb = blk_shadow ?n |- _ =>
              assert (HR : ov_read_bytes segs m (Z_to_bv 64 (SB + E / 8)) 1 = Some [Z_to_bv 8 0])
                by (apply (block_shadow_read0_u segs m SB A n E w); [lia| lia| rewrite <- Eshb; exact BS| lia| lia| lia| lia])
          end
      end
  end;
  zstepA; clear HR; rewrite ?zxb_small, ?sxb_small by lia; zstepA; zstepA; if_false.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia; lia.


(* [comment removed for export] *)
(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition aapp_copy_post (gp tp s5v s6v s10v s11v : word) (F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem)
    (B D1 S nz used1 len1 AF lo SQ sh8 sh9 : Z) (srcb : list byte) (jrest : list byte) : machine_state -> Prop :=
  fun ms' => exists (x1 t0 t1 t2 x8 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR x1 (Z_to_bv 64 SQ) gp tp t0 t1 t2 x8 (Z_to_bv 64 (B + 16)) a0 a1 a2 a3 a4 a5 a6 a7
                 (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 (B + 8)) s5v s6v (Z_to_bv 64 2147450880) (Z_to_bv 64 sh8) (Z_to_bv 64 sh9) s10v s11v t3 t4 t5 t6)
             F1 (Z_to_bv 64 AAPP_EPILOGUE) fc1 None m' (seg_rom bsegs)
    /\ munch [(SQ - 2224, SQ); (D1 + used1, D1 + used1 + nz + 1); (B + 8, B + 12)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
    /\ stk bsegs m' lo SQ
    /\ rw_cells bsegs m' B [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 len1); C4 (Z_to_bv 64 (used1 + nz)); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D1); C8 (Z_to_bv 64 AF)]
    /\ rw_cells bsegs m' (D1 + used1) [CB (Z.to_nat nz) srcb]
    /\ u8arr bsegs m' (D1 + used1 + nz) (Z_to_bv 8 0 :: jrest).

Lemma aapp_copy_seg : forall (P : acc -> Prop) (rav gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s5v s6v s10v s11v t3 t4 t5 t6 : word)
    (F1 : bvmap 5 word) (fc1 : bv 32) (m1 : mem)
    (B D1 S nz used1 len1 AF lo SQ sh8 sh9 : Z) (srcb dstj wsS wsD : list byte) (j0 : byte) (jrest : list byte) (shbB shbD : list byte),
  stk bsegs m1 lo SQ -> mem_inv bsegs m1 -> alloc_ceiling <= lo -> lo + 8192 <= SQ -> SQ + 96 <= 2^47 ->
  rw_cells bsegs m1 B [C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 len1); C4 (Z_to_bv 64 used1); C4 (Z_to_bv 64 0); C8 (Z_to_bv 64 D1); C8 (Z_to_bv 64 AF)] ->
  u8arr bsegs m1 (2147450880 + B / 8) shbB -> shbB = blk_shadow 32 ->
  u8arr bsegs m1 (2147450880 + D1 / 8) shbD -> shbD = blk_shadow len1 ->
  rw_cells bsegs m1 (D1 + used1) [CB (Z.to_nat nz) dstj] -> u8arr bsegs m1 (D1 + used1 + nz) (j0 :: jrest) ->
  bytes_at bsegs m1 S srcb -> length srcb = Z.to_nat nz -> Z.of_nat (length jrest) = len1 - used1 - nz - 1 ->
  icp_globals bsegs m1 2147450880 ->
  shadow_window bsegs m1 2147450880 S nz wsS -> range_clean 2147450880 S nz wsS ->
  shadow_window bsegs m1 2147450880 (D1 + used1) nz wsD -> range_clean 2147450880 (D1 + used1) nz wsD ->
  (* [comment removed for export] *)
  0 < B -> B mod 16 = 0 -> B + 32 <= alloc_ceiling -> 17594333495296 <= B ->
  0 < D1 -> D1 mod 16 = 0 -> D1 + len1 <= alloc_ceiling -> (6303744 <= D1 /\ (D1 + len1 <= 2147446784 \/ 17594333495296 <= D1)) ->
  (B + 32 <= D1 \/ D1 + len1 <= B) ->
  0 <= used1 -> used1 + nz < len1 -> len1 < 2^31 -> 0 < nz -> S <> 0 ->
  (S + nz <= alloc_ceiling \/ S + nz <= 0x31000) ->
  ((0 < S /\ S + nz < 2147450880) \/ 17594333495296 <= S) ->
  (S + nz <= D1 \/ D1 + len1 <= S) -> (S + nz <= B \/ B + 32 <= S) ->
  sh8 = 2147450880 + (B + 16) / 8 -> sh9 = 2147450880 + (B + 8) / 8 ->
  (* [comment removed for export] *)
  pol P (SQ - 2224) SQ -> pol P 0x10000 0x603000 ->
  pol P B (B + 32) -> pol P (2147450880 + B / 8) (2147450880 + B / 8 + 4) ->
  pol P D1 (D1 + len1) -> pol P (2147450880 + D1 / 8) (2147450880 + D1 / 8 + (len1 + 7) / 8) ->
  pol P (shw_lo 2147450880 (D1 + used1)) (shw_hi 2147450880 (D1 + used1) nz) ->
  pol P S (S + nz) -> pol P (shw_lo 2147450880 S) (shw_hi 2147450880 S nz) ->
  evtA bsegs P (aapp_copy_post gp tp s5v s6v s10v s11v F1 fc1 m1 B D1 S nz used1 len1 AF lo SQ sh8 sh9 srcb jrest)
    (MS (mkR rav (Z_to_bv 64 SQ) gp tp t0 t1 t2 (Z_to_bv 64 nz) (Z_to_bv 64 (B + 16)) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 S) (Z_to_bv 64 B) (Z_to_bv 64 (B + 8)) s5v s6v (Z_to_bv 64 2147450880) (Z_to_bv 64 sh8) (Z_to_bv 64 sh9) s10v s11v t3 t4 t5 t6)
        F1 (Z_to_bv 64 AAPP_COPY) fc1 None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until shbD.
  intros ST MI CEIL' LOQ SQH BC BSH BSHeq DSH DSHeq DST ARR3 TB LSRC LJR IG SWS RCS SWD RCD.
  intros B0 B16 BHI BSH2 D0 D16 DHI DSH2 SBD U0 ROOM L31 NPOS SNZ SLO SRIM SSEP SSEPB E8 E9.
  intros PSTK PIMG PB PBS PD PDS PWD PSRC PSHS.
  unfold AAPP_COPY. unfold pol in PB, PBS, PD, PDS.
  pose proof (blk_shadow_length 32 ltac:(lia)) as BSHlen. rewrite <- BSHeq in BSHlen.
  pose proof (blk_shadow_length len1 ltac:(lia)) as DSHlen. rewrite <- DSHeq in DSHlen.
  pose proof (shw_geom 2147450880 (D1 + used1) nz ltac:(lia) ltac:(lia) ltac:(lia)) as GEOD. cbv zeta in GEOD.
  pose proof (shw_geom 2147450880 S nz ltac:(lia) ltac:(lia) ltac:(lia)) as GEOS. cbv zeta in GEOS.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  assert (B8 : B mod 8 = 0) by lia. assert (D8 : D1 mod 8 = 0) by lia. assert (SR : 0 < S /\ S + nz < 2^47) by lia.
  pose proof (munch_refl [(SQ - 2224, SQ); (D1 + used1, D1 + used1 + nz + 1); (B + 8, B + 12)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  (* [comment removed for export] *)
  yhide DST. yhide ARR3. yhide TB. yhide DSH. yhide PSTK. yhide PIMG. yhide PD. yhide PDS. yhide PWD. yhide PSRC. yhide PSHS.
  yhide SLO. yhide SRIM. yhide SSEP. yhide SSEPB. yhide SBD. yhide GEOD. yhide GEOS.
  zstepA. if_cases KA; zify_cond KA. { exfalso. kill KA. }                           (* [comment removed for export] *)
  shadow_reload BSH (B + 16) 8.                                                      (* [comment removed for export] *)
  shadow_reload2 BSH (B + 8) 4.                                                      (* [comment removed for export] *)
  zstepA. rewrite yzx32_small by lia.                                                (* [comment removed for export] *)
  zstepA. rewrite (Z.add_comm used1 D1).                                             (* [comment removed for export] *)
  ugd. zstepA. zstepA. zstepA. ugd.                                                  (* [comment removed for export] *)
  zstepA. zstepA.                                                                    (* [comment removed for export] *)
  stepA.                                                                             (* [comment removed for export] *)
  rewrite (land_M32_small nz) by lia.
  yshow DST. yshow TB. yshow ARR3. yshow DSH. yshow PSTK. yshow PIMG. yshow PD. yshow PWD. yshow PSRC. yshow PSHS.
  yshow SBD. yshow SSEP. yshow SLO. unfold pol in PSTK, PIMG, PWD, PSRC, PSHS.
  stepA.                                                                             (* [comment removed for export] *)
  (* [comment removed for export] *)
  call_spA (asan_memcpy_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (D1 + used1) S nz 2147450880 srcb wsS wsD dstj lo).
  all: rewrite ?USQ.
  all: yshow SRIM; yshow GEOD; yshow GEOS.
  - exact ST.
  - aceil; lia.
  - lia.
  - exact MI.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - lia.
  - unfold range_in_mem, A_HIGHEND_VAL. lia.
  - unfold range_in_mem, A_HIGHEND_VAL. lia.
  - lia.
  - lia.
  - lia.
  - lia.
  - left. lia.
  - right. lia.
  - exact DST.
  - exact TB.
  - exact LSRC.
  - exact IG.
  - exact SWS.
  - exact RCS.
  - destruct DSH2 as [_ [DLO|DHI2]]; [right| left]; lia.
  - exact SWD.
  - exact RCD.
  - destruct DSH2 as [_ [DLO|DHI2]]; [right| left]; lia.
  - exact PSTK.
  - exact PIMG.
  - exact PSRC.
  - intros a k Ha Hk. apply PD; lia.
  - exact PSHS.
  - exact PWD.
  - lazymatch goal with H : stk bsegs ?mx lo _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) => rename H into ST2; rename mx into m2 end.
    lazymatch goal with H : rw_cells bsegs m2 (D1 + used1) _ |- _ => rename H into DST2 end.
    lazymatch goal with H : mem_inv bsegs m2 |- _ => rename H into MI2 end.
    rewrite USQ in ST2.
    (* [comment removed for export] *)
    yhide TB. yhide PSTK. yhide PIMG. yhide PWD. yhide PSRC. yhide PSHS. yhide SLO. yhide SRIM. yhide SSEP. yhide GEOD. yhide GEOS.
    shadow_reload BSH (B + 8) 4.                                                     (* [comment removed for export] *)
    zstepA. rewrite ysx32_small by lia.                                              (* [comment removed for export] *)
    zstepA.                                                                          (* [comment removed for export] *)
    zstepA.                                                                          (* [comment removed for export] *)
    shadow_reload BSH (B + 16) 8.                                                    (* [comment removed for export] *)
    zstepA.                                                                          (* [comment removed for export] *)
    zstepA. zstepA. rewrite (land_M32_small (used1 + nz)) by lia.                   (* [comment removed for export] *)
    zstepA.                                                                          (* [comment removed for export] *)
    replace (D1 + (used1 + nz)) with (D1 + used1 + nz) by lia.
    ugd. zstepA. zstepA. zstepA. ugd. ugd.                                           (* [comment removed for export] *)
    yshow PDS.
    shadow_cases DSH (D1 + used1 + nz) 1.                                            (* [comment removed for export] *)
    2: shadow_slow.
    all: lazymatch goal with |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
           pose proof (u8arr_store_ok_at bsegs mx (D1 + used1 + nz) _ 0 ARR3 ltac:(cbn [length]; lia)) as SOK end.
    all: stepA.                                                                       (* [comment removed for export] *)
    all: lazymatch type of ARR3 with u8arr _ ?mx _ _ =>
           pose proof (u8arr_write bsegs mx (D1 + used1 + nz) _ 0 (Z_to_bv 8 0) ARR3 ltac:(cbn [length]; lia)) as ARR3' end.
    all: cbn [upd Z.to_nat] in ARR3'; rewrite le1_wz by lia; clear ARR3; store_done.
    all: stepA.                                                                       (* [comment removed for export] *)
    all: unfold aapp_copy_post, AAPP_EPILOGUE; finishA.
Qed.

End RC__2.
