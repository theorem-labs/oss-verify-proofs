(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Lib Require Import Arr Bytes ZBridge.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import Shadow.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.BothW Require Import BImg.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface InflateState Inftrees ItableModel.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.LibA Require Import StepF.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U2A Require Import U2AShadow U2AArr U2AKit ItAKit ItAPure.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.U3B Require Import ItB_base.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.asan_ubsan_agrees_alloc_forced_only.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac solve_load ::= first [ solve_load_base | solve_load_sh0 | solve_load_image ].
Local Ltac acc_hint ::= acc_hint_sh.

Section CANSEC1. Context {rc : runConstT}.
Section P.
  Variables (RNG : footprint) (FR : bvmap 5 word) (fc : bv 32) (gp tp : word).
  Variables (SP SPA S F PB top TY : Z) (m1 : amem).
  Variables (lf wf cf : Z -> Z) (lo codes : Z).
  Hypothesis CX : itb_ctx RNG SP SPA S F PB top m1.
  Hypothesis Hcodes : 0 <= codes <= 288.

  Notation LP := (S + 168 + 2 * lo).
  Notation ST := (bst SP SPA S F PB LP TY gp tp FR fc).
  Notation cntAr := (cntA lf lo codes).
  Notation cA := (arr_get (cntA lf lo codes)).
  Notation O k := (OZ (cntA lf lo codes) k).

  Lemma cA_range3 : forall j, 0 <= cA j <= codes.
  Proof. intros j. rewrite cntA_eq. apply cntK_le; lia. Qed.

  Definition offs_post (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (next bitsw : word)
      (x1 x5 x6 x7 x12 x13 x14 x15 x17 x25 x28 x29 x30 x31 : word) : machine_state -> Prop :=
    fun ms' => exists (m : amem) (q10 q11 : word) (of : Z -> Z),
      ms' = ST x1 x5 x6 x7 q10 q11 x12 x13 x14 x15 (Z_to_bv 64 (F + 96)) x17 x25 x28 x29 x30 x31 0x972c4 m
      /\ itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 cA of lf wf cf next bitsw
      /\ (forall k, 1 <= k <= 15 -> of k = arr_get (offsA lf lo codes) k).

  Lemma it_offs : forall (m : amem)
      (v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 : word) (offs : Z -> Z) (next bitsw : word)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 : word),
    itb_inv SPA S F PB m1 m v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 cA offs lf wf cf next bitsw ->
    evtF bsegs RNG (offs_post v0 v8 v16 v24 v32 v40 v48 v56 v64 v72 v80 v88 v96 v104 v112 v120 v128 v136 v144 next bitsw
                              x1 x5 x6 x7 x12 x13 x14 x15 x17 x25 x28 x29 x30 x31)
      (ST x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x25 x28 x29 x30 x31 0x97210 m).
  Proof using All.
    intros until x31. intros INV. open_ctx CX. open_inv INV. unfold bst.
    pose proof (f16arr_to_cells bsegs m (F + 32) 16 _ CNT) as CC.
    cbv [fws map seq Z.of_nat Pos.of_succ_nat Pos.succ] in CC.
    pose proof (f16arr_to_cells bsegs m (F + 96) 16 _ OFFS) as OC.
    cbv [fws map seq Z.of_nat Pos.of_succ_nat Pos.succ] in OC.
    clear CNT OFFS.
    assert (HRa : forall j, 0 <= cA j <= codes) by apply cA_range3.
    assert (OR : forall k, 1 <= k <= 15 -> 0 <= O k <= 14 * 288).
    { intros k Hk. pose proof (OZ_range cntAr 288 k ltac:(lia) ltac:(intros j; pose proof (HRa j); lia) ltac:(lia)). lia. }
    pose proof (HRa 1) as HR1. pose proof (OR 2 ltac:(lia)) as OR2.
    pose proof (HRa 2) as HR2. pose proof (OR 3 ltac:(lia)) as OR3.
    pose proof (HRa 3) as HR3. pose proof (OR 4 ltac:(lia)) as OR4.
    pose proof (HRa 4) as HR4. pose proof (OR 5 ltac:(lia)) as OR5.
    pose proof (HRa 5) as HR5. pose proof (OR 6 ltac:(lia)) as OR6.
    pose proof (HRa 6) as HR6. pose proof (OR 7 ltac:(lia)) as OR7.
    pose proof (HRa 7) as HR7. pose proof (OR 8 ltac:(lia)) as OR8.
    pose proof (HRa 8) as HR8. pose proof (OR 9 ltac:(lia)) as OR9.
    pose proof (HRa 9) as HR9. pose proof (OR 10 ltac:(lia)) as OR10.
    pose proof (HRa 10) as HR10. pose proof (OR 11 ltac:(lia)) as OR11.
    pose proof (HRa 11) as HR11. pose proof (OR 12 ltac:(lia)) as OR12.
    pose proof (HRa 12) as HR12. pose proof (OR 13 ltac:(lia)) as OR13.
    pose proof (HRa 13) as HR13. pose proof (OR 14 ltac:(lia)) as OR14.
    pose proof (HRa 14) as HR14. pose proof (OR 15 ltac:(lia)) as OR15.
    zs. zs. zs. ubg. zs.
    zs. rewrite (sx16_small (cA 1)) by lia.
    setreg 10 (Z_to_bv 64 (O 2)) ltac:(rewrite (OZ_S' cntAr 2) by lia; change (2 - 1) with 1; rewrite OZ_1; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 2)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 3)) ltac:(rewrite (OZ_S' cntAr 3) by lia; change (3 - 1) with 2; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 3)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 4)) ltac:(rewrite (OZ_S' cntAr 4) by lia; change (4 - 1) with 3; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 4)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 5)) ltac:(rewrite (OZ_S' cntAr 5) by lia; change (5 - 1) with 4; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 5)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 6)) ltac:(rewrite (OZ_S' cntAr 6) by lia; change (6 - 1) with 5; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 6)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 7)) ltac:(rewrite (OZ_S' cntAr 7) by lia; change (7 - 1) with 6; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 7)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 8)) ltac:(rewrite (OZ_S' cntAr 8) by lia; change (8 - 1) with 7; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 8)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 9)) ltac:(rewrite (OZ_S' cntAr 9) by lia; change (9 - 1) with 8; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 9)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 10)) ltac:(rewrite (OZ_S' cntAr 10) by lia; change (10 - 1) with 9; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 10)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 11)) ltac:(rewrite (OZ_S' cntAr 11) by lia; change (11 - 1) with 10; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 11)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 12)) ltac:(rewrite (OZ_S' cntAr 12) by lia; change (12 - 1) with 11; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 12)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 13)) ltac:(rewrite (OZ_S' cntAr 13) by lia; change (13 - 1) with 12; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 13)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 14)) ltac:(rewrite (OZ_S' cntAr 14) by lia; change (14 - 1) with 13; f_equal; lia).
    zs.
    zs. rewrite (sx16_small (cA 14)) by lia. zs.
    setreg 10 (Z_to_bv 64 (O 15)) ltac:(rewrite (OZ_S' cntAr 15) by lia; change (15 - 1) with 14; f_equal; lia).
    zs.
    pose (of := fun k : Z => if k =? 0 then offs 0 else if k =? 1 then 0 else O k).
    assert (OFFS : f16arr bsegs m0 (F + 96) 16 of) by (apply f16arr_of_cells_fws; exact OC).
    assert (CNT : f16arr bsegs m0 (F + 32) 16 cA) by (apply f16arr_of_cells_fws; exact CC).
    clear OC CC.
    apply evtF_done. unfold offs_post. exists m0. do 2 eexists. exists of. split; [reflexivity|]. split; [close_inv|].
    intros k Hk. unfold offsA. rewrite (offs_spec cntAr) by (first [ intros j; pose proof (HRa j); lia | lia ]).
    unfold of. destruct (Z.eqb_spec k 0); [lia|]. destruct (Z.eqb_spec k 1) as [->|]; [rewrite OZ_1; reflexivity | reflexivity].
  Qed.
End P.
End CANSEC1.
