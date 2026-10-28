From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Spec Require Import FseNCount FseLemmas HufPure_FseDecomp HufPure_FseDecompRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Import FseWalkKit FseWalkMem FseWalkArith StrFun FseRdKit.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Ubsan Require Import UImg RF_huf_tbl_iface RF_huf_tbl_kit RF_huf_bdt_model
  RF_huf_bdt_bld.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Lib Require Import Step MState.
From OssFuzzTheorems.Proofs.zstd.huf_decompress.lib.Common Require Stdio_pure.

Lemma bdt_evt_R : forall segs Q R R' F pc fc (mm rom : word -> option byte),
  evt segs Q (MS R' F pc fc None mm rom) -> R' = R -> evt segs Q (MS R F pc fc None mm rom).
Proof. intros segs Q R R' F pc fc mm rom H E. subst. exact H. Qed.
Import ListNotations.
Open Scope Z_scope.

Section Tail.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m : fmem) (DT WK msv tl fm lo : Z).
  Notation SP := (bv_unsigned sp).
  Hypothesis HTL : 1 <= tl <= 12.
  Hypothesis HMSV : 0 <= msv <= 255.
  Hypothesis HFM : 0 <= fm <= 1.
  Hypothesis HDT : 0 < DT /\ DT + FSE_DTABLE_SIZE tl <= 2^64.
  Hypothesis HWK : 0 < WK /\ WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= 2^64.
  Hypothesis DTW : DT + FSE_DTABLE_SIZE tl <= WK \/ WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= DT.
  Hypothesis HLO : lo <= SP - FSE_BUILD_STACK.
  Hypothesis DLO : DT + FSE_DTABLE_SIZE tl <= lo \/ SP <= DT.
  Hypothesis WLO : WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv <= lo \/ SP <= WK.

  Lemma bdt_tail : forall m1 (syms : list (option Z)) (snext : list Z) (jt : list byte) (cells : list dcell)
      (x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 : word),
    build_loop tl (Z.to_nat (2^tl)) 0 syms snext [] = Ok cells ->
    length syms = Z.to_nat (2^tl) -> length jt = (4 * Z.to_nat (2^tl))%nat ->
    zlen snext = msv + 1 -> Forall (fun v => 0 <= v < 65536) snext ->
    u8arr usegs m1 DT (le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fm)) ->
    u8arr usegs m1 (DT + 4) (tsym jt syms) ->
    u8arr usegs m1 WK (u16s (map (Z_to_bv 64) snext)) ->
    rw_cells usegs m1 (SP - 128) [C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (WK + 2 * msv)); C8 (Z_to_bv 64 tl);
      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    stk usegs m1 lo (SP - 128) ->
    munch [(SP - FSE_BUILD_STACK, SP); (DT, DT + FSE_DTABLE_SIZE tl); (WK, WK + FSE_BUILD_DTABLE_WKSP_SIZE tl msv)] m m1 ->
    wmono usegs m m1 -> mem_inv usegs m1 ->
    evt usegs (fse_build_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc DT WK msv tl (mkDT tl fm cells) lo m)
      (MS (mkR x1 (Z_to_bv 64 (SP - 128)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13
               (Z_to_bv 64 WK) (Z_to_bv 64 (2^tl)) (Z_to_bv 64 (Z.lxor WK 18446744073709551615)) (Z_to_bv 64 (DT + 4))
               x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
          F (Z_to_bv 64 0x1f508) fc None m1 (seg_rom usegs)).
  Proof using All.
    intros m1 syms snext jt cells x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31
      BL LSY LJT LSN FSN HDR TAB WKA FR STK MU WM MI.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    unfold FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE, FSE_BUILD_STACK in *.
    assert (P2 : 2 <= 2^tl <= 4096) by (split; [change 2 with (2^1); apply Z.pow_le_mono_r|change 4096 with (2^12); apply Z.pow_le_mono_r]; lia).
    repeat (lazymatch goal with
            | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
                let b := eval vm_compute in (pc =? PFSE_BUILD_DT + 1008) in lazymatch b with false => zstep end
            end).
    pose proof (rw_cells_bound usegs _ _ _ FR) as FRB. cbn [cells_size csize Nat.add] in FRB.
    assert (FR16 : rw_cells usegs m1 (SP - 128 + 16) [C8 (Z_to_bv 64 tl)]).
    { apply Stdio_pure.rw_cells_app with (cs1 := [C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (WK + 2 * msv))]) in FR.
      destruct FR as [_ FR2]. cbn [cells_size csize Nat.add Z.of_nat] in FR2.
      apply Stdio_pure.rw_cells_app with (cs1 := [C8 (Z_to_bv 64 tl)]) in FR2.
      destruct FR2 as [FR3 _]. replace (SP - 128 + 16) with (SP - 128 + Z.of_nat 16) by reflexivity. exact FR3. }
    eapply bdt_evt_R.
    1: eapply bl_loop with (m := m1) (M1 := msv + 1) (TD := DT + 4) (tl := tl) (WK := WK) (jt := jt) (syms := syms)
        (sp := Z_to_bv 64 (SP - 128)) (f := Z.to_nat (2^tl)) (u := 0) (acc := []) (snext := snext) (r := cells).
    all: try (lazymatch goal with |- mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _ =>
                replace (DT + 4 + 3 + 4 * 0) with (DT + 7) by lia;
                replace (2 ^ tl - 0) with (2 ^ tl) by lia;
                replace (DT + 4 + 4 * 0) with (DT + 4) by lia;
                unfold mkR; reflexivity end).
    all: try (lazymatch goal with |- word => exact (Z_to_bv 64 0) end).
    all: lazymatch goal with
         | |- build_loop _ _ _ _ _ _ = _ => exact BL
         | |- Forall _ _ => exact FSN
         | |- rw_cells _ _ _ _ => rewrite unsigned_lit by lia; exact FR16
         | |- bl_sep _ _ _ _ _ => unfold bl_sep; rewrite unsigned_lit by lia; lia
         | |- bl_inv _ _ _ _ _ _ _ _ _ _ _ =>
             unfold bl_inv; cbn [concat map skipn app Nat.mul Z.to_nat];
             split; [exact TAB|]; split; [exact WKA|]; split; [apply munch_refl|]; split; [apply wmono_refl| exact MI]
         | |- forall _, _ =>
             let m2 := fresh "m2" in let sn' := fresh "sn'" in
             intros m2 sn' y10 y13 y28 y29 y30 y31 LR INV FRT
         | |- _ => first [assumption | (rewrite ?Z2Nat.id by lia; lia) | reflexivity]
         end.
    destruct INV as (TAB2 & WKA2 & MU2 & WM2 & MI2).
    assert (FR2 : rw_cells usegs m2 (SP - 128) [C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (WK + 2 * msv)); C8 (Z_to_bv 64 tl);
      C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { eapply rw_cells_transport; [exact FR | exact MU2 | exact WM2 | cbn [cells_size csize Nat.add disjoint_from]; lia]. }
    assert (STK2 : stk usegs m2 lo (SP - 128)).
    { eapply stk_transport_disjoint; [exact STK | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    assert (HDR2 : u8arr usegs m2 DT (le2 (Z_to_bv 64 tl) ++ le2 (Z_to_bv 64 fm))).
    { eapply u8arr_transport; [exact HDR | exact MU2 | exact WM2 | rewrite length_app, !length_le2; cbn [disjoint_from]; lia]. }
    clear FR FRT FR16 STK HDR.
    repeat (lazymatch goal with |- evt _ _ (MS _ _ (Z_to_bv 64 _) _ _ _ _) => zstep end).
    release_frame FR2 STK2 (bv_unsigned sp).
    replace (SP - 128 + 128) with SP by lia. rewrite Z_to_bv_bv_unsigned.
    apply evt_done. unfold fse_build_post.
    do 14 eexists. exists m2.
    split; [reflexivity|].
    unfold FSE_DTABLE_SIZE, FSE_BUILD_DTABLE_WKSP_SIZE, FSE_BUILD_STACK.
    split; [eapply munch_trans; [exact MU | eapply munch_weaken; [| exact MU2]; unfold sub_fp; intros ?x; cbn; intuition lia]|].
    split; [eapply wmono_trans; [exact WM | exact WM2]|].
    split; [exact MI2|].
    split; [exact STK2|].
    rewrite (skipn_all2 jt) in TAB2 by (rewrite LJT; lia).
    rewrite (skipn_all2 syms) in TAB2 by (rewrite LSY; lia).
    cbn [tsym] in TAB2. rewrite app_nil_r in TAB2.
    unfold fse_dt_bytes; cbn [dt_tableLog dt_fastMode dt_cells]. rewrite app_assoc.
    apply (proj2 (RF_huf_bdt_model.u8arr_app usegs _ _ _ _)). split; [exact HDR2|].
    rewrite length_app, !length_le2. replace (DT + Z.of_nat (2 + 2)) with (DT + 4) by lia. exact TAB2.
  Qed.
End Tail.
