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
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BY_ubkit B_iface BI_shadow BI_globals2 BI_region_is_poisoned BI_asan_memset BYajlRep BYajl_iface BY_hand BY_alloc1 BY_alloc2.
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
Definition AAL_RET5 : Z := 0x825d8.   (* [comment removed for export] *)

End RC__1.
Ltac kill K := exfalso; revert K; unfold wz; rewrite ?unsigned_lit by lia;
  try (change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones by lia; rewrite ?Z.mod_small by lia); lia.

(* [comment removed for export] *)
Section RC__2.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition hcells15 (CBK CX L : Z) (pew : word) (bc : word) (pad DB SB SZ U YF : word) : list cell :=
  [C8 (Z_to_bv 64 CBK); C8 (Z_to_bv 64 CX); C8 (Z_to_bv 64 L); C8 pew; C4 bc; C4 pad; C8 DB; C8 SB; C4 SZ; C4 U; C8 YF;
   C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma aal5_seg : forall (P : acc -> Prop) (sp gp tp t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 s9v : word)
    (F : bvmap 5 word) (fc : bv 32) (m1 : mem) (SQ ff lo H CBK CFGP CX L : Z) (hj : list byte) (shH : list byte),
  mem_inv bsegs m1 -> 0 <= SQ -> SQ + 192 <= 2^47 ->
  rw_cells bsegs m1 H [C8 (Z_to_bv 64 CBK); C8 (Z_to_bv 64 CX); CB 56 hj] ->
  rw_cells bsegs m1 (H + 72) [C8 (Z_to_bv 64 AY_MALLOC_W); C8 (Z_to_bv 64 AY_REALLOC_W); C8 (Z_to_bv 64 AY_FREE_W); C8 (Z_to_bv 64 0)] ->
  u8arr bsegs m1 (2147450880 + H / 8) shH -> shH = blk_shadow 104 ->
  17594333495296 <= H -> H + 104 <= alloc_ceiling -> H mod 16 = 0 -> 0 < L < 2^64 ->
  pol P H (H + 104) -> pol P (2147450880 + H / 8) (2147450880 + H / 8 + 13) ->
  evtA bsegs P (fun ms' => exists (a1' a2' : word) (pew bc pad DB SB SZ U YF : word) (m' : mem),
      munch [(H, H + 104)] m1 m' /\ wmono bsegs m1 m' /\ mem_inv bsegs m'
      /\ u8arr bsegs m' (2147450880 + H / 8) shH
      /\ rw_cells bsegs m' H (hcells15 CBK CX L pew (Z_to_bv 64 0) pad DB SB SZ U YF)
      /\ ms' = MS (mkR (Z_to_bv 64 AAL_RET5) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 (H + 72)) a1' a2' a3 a4 a5 a6 a7
                   (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 CFGP) (Z_to_bv 64 (H + 72)) s9v (Z_to_bv 64 (ff + 56)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
                   F (Z_to_bv 64 AY_BUF_ALLOC) fc None m' (seg_rom bsegs))
    (MS (mkR (Z_to_bv 64 AAL_RET4) (Z_to_bv 64 SQ) gp tp t0 t1 t2 sp (Z_to_bv 64 SQ) (Z_to_bv 64 L) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 ff) (Z_to_bv 64 H) (Z_to_bv 64 (ff + 32)) (Z_to_bv 64 2147450880) (Z_to_bv 64 ff) (Z_to_bv 64 CFGP) (Z_to_bv 64 (H + 72)) s9v (Z_to_bv 64 (ff + 56)) (Z_to_bv 64 (ff / 8 + 2147450880)) t3 t4 t5 t6)
        F (Z_to_bv 64 AAL_RET4) fc None m1 (seg_rom bsegs)).
Proof. aceil.
  intros until shH. intros MI SQ0 SQH HC HA HS HSeq HR1 HR2 H16 LR PH PHS.
  unfold pol, AAL_RET4, AAL_RET5, AY_BUF_ALLOC, hcells15, AY_MALLOC_W, AY_REALLOC_W, AY_FREE_W in *.
  pose proof (blk_shadow_length 104 ltac:(lia)) as HSlen. rewrite <- HSeq in HSlen.
  assert (H8 : H mod 8 = 0) by lia.
  assert (USQ : bv_unsigned (Z_to_bv 64 SQ) = SQ) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  apply (rw_cells_split_CB bsegs _ _ [_; _] 56 _ [] [8;8;4;4;8;8;4;4;8]%nat) in HC; [| reflexivity]. cbn [app mk_CB_cells] in HC.
  awordify HC.
  lazymatch type of HC with rw_cells _ _ _ ?cs1 => lazymatch type of HA with rw_cells _ _ _ ?cs2 =>
    assert (HCA : rw_cells bsegs m1 H (cs1 ++ cs2)) by (apply (proj2 (ycells_app bsegs _ _ cs1 cs2)); split; [exact HC| cbn [cells_size csize Nat.add]; exact HA]) end end.
  clear HC HA. cbn [app] in HCA.
  pose proof (munch_refl [(H, H + 104)] m1) as MU. pose proof (wmono_refl bsegs m1) as WM.
  zstepA.                                                 (* [comment removed for export] *)
  shadow_fast HS (H + 16) 8.                              (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  zstepA. if_cases K0; zify_cond K0. { kill K0. }          (* [comment removed for export] *)
  zstepA. shadow_fast HS (H + 32) 4.                      (* [comment removed for export] *)
  zstepA.                                                 (* [comment removed for export] *)
  stepA. stepA.                                           (* [comment removed for export] *)
  apply evtA_done. lazymatch goal with H1 : rw_cells bsegs ?mx H [_; _; _; C8 ?pew; C4 ?bc; C4 ?pad; C8 ?db; C8 ?sb; C4 ?sz; C4 ?u; C8 ?yf; _; _; _; _] |- _ =>
    eexists _, _, pew, bc, pad, db, sb, sz, u, yf, mx end.
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|].
  split; [assumption| reflexivity].
Qed.
End RC__2.
